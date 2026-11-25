-- Prove2me | Theorems.Thm_PI_HwUniqW_Hpk_conjTranspose
-- name    : PI.HwUniqW.Hpk_conjTranspose
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:32:26.588667+00:00
-- url     : https://prove2.me/theorems/86be9260-57e9-4fca-9f3f-1b2eea5dbce8
-- title:
--   Hw Uniq W: Hpk conj Transpose
-- statement:
--   The Hw Uniq W construction uses the Hpk conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/HpkMulMulHpkApply.lean#L86-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/HpkMulMulHpkApply.lean#L86-L93

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

theorem PI.HwUniqW.Hpk_conjTranspose : (Hpk k r)ᴴ = Hpk k r := by sorry
