-- Prove2me | Theorems.Thm_ShiTM_stepAux_trStmt_one_simulation
-- name    : ShiTM.stepAux_trStmt_one_simulation
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-14T19:38:14.880272+00:00
-- url     : https://prove2.me/theorems/90638f3a-59ca-49a7-ab90-16ae0a4d4749
-- title:
--   A translated component program simulates the original step for step
-- statement:
--   Executing the translation of a component machine's program on a lifted configuration of the composite machine produces exactly the lift of the configuration the original program produces: the same changes to the component's own stacks, the background stacks of the other component and the scratch stack untouched, and the other component's internal state and the transfer register unchanged.
--
--   The labels diverge in exactly one way, and deliberately. Where the original program reaches a jump, the translation reaches the image of that label; where the original reaches its halt, the translation instead jumps to the entry of the transfer loop. That redirection is the reason the translation exists: a halted machine takes no further steps, so a composite cannot resume a component's program unchanged. Both cases are recorded separately, and they concern the leaf actually reached, since a single step executes an entire program tree.

import Definitions.Def_ShiTM2_Composite

set_option autoImplicit false

namespace ShiTM

open Turing.TM2 ShiTM2

theorem stepAux_trStmt_one_simulation (tm₁ tm₂ : Turing.FinTM2) [DecidableEq tm₁.K]
    [DecidableEq (CompK tm₁ tm₂)] (T : ∀ k, List (CompΓ tm₁ tm₂ k)) :
    (∀ (q : Stmt tm₁.Γ tm₁.Λ tm₁.σ) (w : Compσ tm₁ tm₂) (S : ∀ i, List (tm₁.Γ i)),
        stepAux (trStmt₁ tm₁ tm₂ q) w (liftStk₁ tm₁ tm₂ T S)
          = liftCfg₁ tm₁ tm₂ T w.2.1 w.2.2 (stepAux q w.1 S))
  ∧ (∀ (q : Stmt tm₁.Γ tm₁.Λ tm₁.σ) (w : Compσ tm₁ tm₂) (S : ∀ i, List (tm₁.Γ i)),
        (stepAux (trStmt₁ tm₁ tm₂ q) w (liftStk₁ tm₁ tm₂ T S)).var
            = ((stepAux q w.1 S).var, w.2.1, w.2.2)
      ∧ (stepAux (trStmt₁ tm₁ tm₂ q) w (liftStk₁ tm₁ tm₂ T S)).stk
            = liftStk₁ tm₁ tm₂ T (stepAux q w.1 S).stk)
  ∧ (∀ (q : Stmt tm₁.Γ tm₁.Λ tm₁.σ) (w : Compσ tm₁ tm₂) (S : ∀ i, List (tm₁.Γ i))
        (l : tm₁.Λ), (stepAux q w.1 S).l = Option.some l →
        (stepAux (trStmt₁ tm₁ tm₂ q) w (liftStk₁ tm₁ tm₂ T S)).l
          = Option.some (injΛ₁ tm₁ tm₂ l))
  ∧ (∀ (q : Stmt tm₁.Γ tm₁.Λ tm₁.σ) (w : Compσ tm₁ tm₂) (S : ∀ i, List (tm₁.Γ i)),
        (stepAux q w.1 S).l = Option.none →
        (stepAux (trStmt₁ tm₁ tm₂ q) w (liftStk₁ tm₁ tm₂ T S)).l
          = Option.some (lcopyA tm₁ tm₂)) := by
  sorry

end ShiTM
