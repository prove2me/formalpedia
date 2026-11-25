-- Prove2me | Theorems.Thm_PI_ExpIntWProof_Key_div_p_mem_of_S
-- name    : PI.ExpIntWProof.Key.div_p_mem_of_S
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:11.032224+00:00
-- url     : https://prove2.me/theorems/82b10f5e-117e-582c-88d5-ebe4b1514e05
-- title:
--   Key: div p mem of S
-- statement:
--   The Key construction uses the div p mem of S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialIntegrality/RootsOfUnityRingLeWittIntegers.lean#L106-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialIntegrality/RootsOfUnityRingLeWittIntegers.lean#L106-L131

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_RootsOfUnityRingLeWittIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.ExpIntWProof PI.ExpIntWProof.Key
variable {p : ℕ} [hp : Fact p.Prime]

theorem PI.ExpIntWProof.Key.div_p_mem_of_S {y : ℂ_[p]} (hy : y ∈ S0 p) (h : ‖y‖ < 1) : y / p ∈ Wp p := by sorry
