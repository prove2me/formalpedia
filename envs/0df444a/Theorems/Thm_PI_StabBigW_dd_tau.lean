-- Prove2me | Theorems.Thm_PI_StabBigW_dd_tau
-- name    : PI.StabBigW.dd_tau
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:28:24.285995+00:00
-- url     : https://prove2.me/theorems/4b84b3c8-8f08-5e7c-a673-74c0e8dabba0
-- title:
--   Stab Big W: dd tau
-- statement:
--   The Stab Big W construction uses the dd tau property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LargeStabilizerInverse/GLeftInv.lean#L187-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LargeStabilizerInverse/GLeftInv.lean#L187-L205

import Definitions.Def_Formalism_PeriodIntegrals_StabBig
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LargeStabilizerInverse_GLeftInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.StabBigW
open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
variable {k r : ℕ}

theorem PI.StabBigW.dd_tau {c : Fin r → ℂ} (hc : ∀ a, c a ≠ 0) (j : Fin (2 * r + k + 1))
    (hj : j.val < r ∨ r + k < j.val) :
    dd k r (fun a => star (c a)) (tau k r j) * dd k r c j = 1 := by sorry
