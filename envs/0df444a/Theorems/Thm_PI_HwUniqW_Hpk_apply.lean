-- Prove2me | Theorems.Thm_PI_HwUniqW_Hpk_apply
-- name    : PI.HwUniqW.Hpk_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:30:19.496017+00:00
-- url     : https://prove2.me/theorems/4f2f3431-179e-4eab-a70e-4c62ad39393a
-- title:
--   Hw Uniq W: Hpk apply
-- statement:
--   The Hw Uniq W construction uses the Hpk apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/HpkMulMulHpkApply.lean#L42-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/HpkMulMulHpkApply.lean#L42-L51

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

theorem PI.HwUniqW.Hpk_apply (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = piI k r i then epsI k r i else 0 := by sorry
