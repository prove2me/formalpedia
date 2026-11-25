-- Prove2me | Theorems.Thm_P2M_PI_HwUniqW_inv_mul_UH__9fc24965c5a2
-- name    : P2M_PI_HwUniqW_inv_mul_UH__9fc24965c5a2
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:41:52.216019+00:00
-- url     : https://prove2.me/theorems/622cc32e-2438-41c0-8bc3-81d5627119bc
-- title:
--   P2 M PI Hw Uniq W inv mul UH  9fc24965c5a2: P2 M PI Hw Uniq W inv mul UH  9fc24965c5a2
-- statement:
--   The P2 M PI Hw Uniq W inv mul UH  9fc24965c5a2 construction uses the P2 M PI Hw Uniq W inv mul UH  9fc24965c5a2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/HpkMulMulHpkApply.lean#L110-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/HpkMulMulHpkApply.lean#L110-L113

import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
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
open PI PI.HwUniqW
open PI.UpqRep
variable {k r : ℕ}

theorem P2M_PI_HwUniqW_inv_mul_UH__9fc24965c5a2 {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    g⁻¹ * g = 1 := by sorry

alias «PI».«HwUniqW».«inv_mul_UH'» := P2M_PI_HwUniqW_inv_mul_UH__9fc24965c5a2
