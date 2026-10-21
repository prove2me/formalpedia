-- Prove2me | Theorems.Thm_TeamDelegation_Optimal_threshold_order
-- name    : TeamDelegation.Optimal.threshold_order
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:29.013838+00:00
-- url     : https://prove2.me/theorems/602ecda1-f1b5-49b5-b992-bb5abfea43d0
-- title:
--   Proposition 3: strict ordering of delegation thresholds
-- statement:
--   Under the model's standing assumptions and Assumption 1, the delegation thresholds satisfy
--
--   $$0<\widehat\Delta_A<\Delta_A^{\mathrm{crit}}<\Delta_A^{\max},\qquad 0<\Delta_B^{\max}.$$
--
--   This orders the range of A's adoption-cost difference where delegation changes its punishment equilibrium and separates the two formulas for A's delegated bonus.
--
--   **Formalization Note** The nonnegative probability bounds and $r<1$ are explicit standing assumptions; they also ensure that the defining denominators are nonzero.
-- source:
--   Upton, Implicit Incentives and Delegation in Teams, TRR 266 Working Paper No. 67 (SSRN 3991736, 17 Dec 2021), p. 34 (PDF 35), end of proof of Proposition 3; equations (19)–(20) on p. 18 (PDF 19)

import Mathlib
import Definitions.Def_TeamDelegation_Optimal_Model

namespace TeamDelegation.Optimal

/-- Proposition 3 and its proof, pp. 18 and 34: the delegation thresholds
are strictly ordered in the stated regime. -/
theorem threshold_order (P : Params) (hS : P.Standing)
    (hA1 : P.Assumption1) :
    0 < DeltaMaxA P ∧ 0 < DeltaMaxB P ∧
      0 < DeltaHatA P ∧ DeltaHatA P < DeltaCritA P ∧
      DeltaCritA P < DeltaMaxA P := by sorry

end TeamDelegation.Optimal
