-- Prove2me | Theorems.Thm_ShiTM_stepAux_trStmt_two_simulation
-- name    : ShiTM.stepAux_trStmt_two_simulation
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-14T20:54:44.306679+00:00
-- url     : https://prove2.me/theorems/8175d49c-3fd9-4e53-b5b1-4a3e49212be3
-- title:
--   The second component's translated program also simulates the original step for step
-- statement:
--   Executing the translation of the second component machine's program on a lifted configuration of the composite machine produces exactly the lift of the configuration the original program produces: the same changes to that component's own stacks, the first component's stacks and the scratch stack untouched, and the first component's internal state and the transfer register unchanged.
--
--   Unlike the first component, the labels require no special case. The first component's translation has to redirect its halt into the transfer loop, because a halted machine takes no further steps and the composite must still run the second program afterwards. The second component is the last to run, so its halt is the composite's halt and is left alone. Consequently a single equation covers every leaf the step can reach: the label of the translated program's result is the image of the original's label under the relabelling, read as a partial function, with a jump mapping to the image of its target and a halt mapping to a halt.

import Definitions.Def_ShiTM2_Composite

set_option autoImplicit false

namespace ShiTM

open Turing.TM2 ShiTM2

theorem stepAux_trStmt_two_simulation (tm₁ tm₂ : Turing.FinTM2) [DecidableEq tm₂.K]
    [DecidableEq (CompK tm₁ tm₂)] (T : ∀ k, List (CompΓ tm₁ tm₂ k)) :
    (∀ (q : Stmt tm₂.Γ tm₂.Λ tm₂.σ) (w : Compσ tm₁ tm₂) (S : ∀ i, List (tm₂.Γ i)),
        stepAux (trStmt₂ tm₁ tm₂ q) w (liftStk₂ tm₁ tm₂ T S)
          = liftCfg₂ tm₁ tm₂ T w.1 w.2.2 (stepAux q w.2.1 S))
  ∧ (∀ (q : Stmt tm₂.Γ tm₂.Λ tm₂.σ) (w : Compσ tm₁ tm₂) (S : ∀ i, List (tm₂.Γ i)),
        (stepAux (trStmt₂ tm₁ tm₂ q) w (liftStk₂ tm₁ tm₂ T S)).var
            = (w.1, (stepAux q w.2.1 S).var, w.2.2)
      ∧ (stepAux (trStmt₂ tm₁ tm₂ q) w (liftStk₂ tm₁ tm₂ T S)).stk
            = liftStk₂ tm₁ tm₂ T (stepAux q w.2.1 S).stk)
  ∧ (∀ (q : Stmt tm₂.Γ tm₂.Λ tm₂.σ) (w : Compσ tm₁ tm₂) (S : ∀ i, List (tm₂.Γ i)),
        (stepAux (trStmt₂ tm₁ tm₂ q) w (liftStk₂ tm₁ tm₂ T S)).l
          = ((stepAux q w.2.1 S).l).map (injΛ₂ tm₁ tm₂)) := by
  sorry

end ShiTM
