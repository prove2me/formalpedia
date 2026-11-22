-- Prove2me | Theorems.Thm_ShiTM_initList_haltList_comp
-- name    : ShiTM.initList_haltList_comp
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-14T21:44:38.58149+00:00
-- url     : https://prove2.me/theorems/8c827b9b-13c5-4762-b35d-fde774f3538d
-- title:
--   Initial and halting configurations of the sequential composite machine
-- statement:
--   The initial and final configurations of the composite machine are computed explicitly. The composite starts at the image of the first machine's start label, in the composite's own initial state, with the given input on the image of the first machine's input stack and every other stack empty; it halts with no label, in the initial state again, with the output on the image of the second machine's output stack and every other stack empty.
--
--   The two clauses that matter for later use concern the first machine's stacks. The composite's initial stacks, read along the first machine's stack injection, are exactly the first machine's own initial stacks, and the second machine's stacks together with the scratch stack all start empty. The first of these is what allows the step-exact simulation of the first component to be applied at the genuine starting configuration rather than at an abstract lifted one, and so is the bridge between the boundary conditions that the definition of computation imposes and the statements about runs proved separately.

import Definitions.Def_ShiTM2_Composite
import Theorems.Thm_ShiTM_initList_haltList_laws

set_option autoImplicit false

namespace ShiTM

open ShiTM2

theorem initList_haltList_comp (tm₁ tm₂ : Turing.FinTM2) (tr : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (dflt : tm₂.Γ tm₂.k₀)
    (s : List ((comp tm₁ tm₂ tr dflt).Γ (comp tm₁ tm₂ tr dflt).k₀))
    (t : List ((comp tm₁ tm₂ tr dflt).Γ (comp tm₁ tm₂ tr dflt).k₁)) :
    (Turing.initList (comp tm₁ tm₂ tr dflt) s).l
        = Option.some (injΛ₁ tm₁ tm₂ tm₁.main)
      ∧ (Turing.initList (comp tm₁ tm₂ tr dflt) s).var = compInitialState tm₁ tm₂
      ∧ (Turing.initList (comp tm₁ tm₂ tr dflt) s).stk (injK₁ tm₁ tm₂ tm₁.k₀) = s
      ∧ (∀ k : CompK tm₁ tm₂, k ≠ injK₁ tm₁ tm₂ tm₁.k₀ →
          (Turing.initList (comp tm₁ tm₂ tr dflt) s).stk k = [])
      ∧ (Turing.haltList (comp tm₁ tm₂ tr dflt) t).l = Option.none
      ∧ (Turing.haltList (comp tm₁ tm₂ tr dflt) t).var = compInitialState tm₁ tm₂
      ∧ (Turing.haltList (comp tm₁ tm₂ tr dflt) t).stk (injK₂ tm₁ tm₂ tm₂.k₁) = t
      ∧ (∀ k : CompK tm₁ tm₂, k ≠ injK₂ tm₁ tm₂ tm₂.k₁ →
          (Turing.haltList (comp tm₁ tm₂ tr dflt) t).stk k = [])
      ∧ (∀ i : tm₁.K, (Turing.initList (comp tm₁ tm₂ tr dflt) s).stk (injK₁ tm₁ tm₂ i)
          = (Turing.initList tm₁ s).stk i)
      ∧ (∀ i : tm₂.K,
          (Turing.initList (comp tm₁ tm₂ tr dflt) s).stk (injK₂ tm₁ tm₂ i) = [])
      ∧ (Turing.initList (comp tm₁ tm₂ tr dflt) s).stk (kScr tm₁ tm₂) = [] := by
  sorry

end ShiTM
