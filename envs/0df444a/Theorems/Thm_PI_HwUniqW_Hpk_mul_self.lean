-- Prove2me | Theorems.Thm_PI_HwUniqW_Hpk_mul_self
-- name    : PI.HwUniqW.Hpk_mul_self
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:21.14008+00:00
-- url     : https://prove2.me/theorems/fe1b07f8-f744-4b4d-92b3-812e4cc767db
-- title:
--   Hw Uniq W: Hpk mul self
-- statement:
--   The Hw Uniq W construction uses the Hpk mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/HpkMulMulHpkApply.lean#L78-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/HpkMulMulHpkApply.lean#L78-L84

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

theorem PI.HwUniqW.Hpk_mul_self : Hpk k r * Hpk k r = 1 := by sorry
