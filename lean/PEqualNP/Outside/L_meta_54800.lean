import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 4000 in
theorem PEqualNP.Outside.L_meta_54800 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274910131 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [2, 3]⟩, ⟨.or, [2, 1]⟩, ⟨.and, [6, 0]⟩,
    ⟨.and, [7, 4]⟩, ⟨.or, [9, 8]⟩, ⟨.or, [7, 0]⟩,
    ⟨.or, [5, 10]⟩, ⟨.not, [12]⟩, ⟨.and, [11, 5]⟩, ⟨.or, [14, 13]⟩], 15⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
