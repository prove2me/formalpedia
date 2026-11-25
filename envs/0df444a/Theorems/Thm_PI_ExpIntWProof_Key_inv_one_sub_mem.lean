-- Prove2me | Theorems.Thm_PI_ExpIntWProof_Key_inv_one_sub_mem
-- name    : PI.ExpIntWProof.Key.inv_one_sub_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:19.506869+00:00
-- url     : https://prove2.me/theorems/7b8e8e08-fcd5-4da1-b2bb-3d10830f2c33
-- title:
--   Key: inv one sub mem
-- statement:
--   The Key construction uses the inv one sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialIntegrality/RootsOfUnityRingLeWittIntegers.lean#L99-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialIntegrality/RootsOfUnityRingLeWittIntegers.lean#L99-L102

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

theorem PI.ExpIntWProof.Key.inv_one_sub_mem {ξ : ℂ_[p]} (hξ : ξ ∈ Wp p) (h : ‖ξ‖ < 1) : (1 - ξ)⁻¹ ∈ Wp p := by sorry
