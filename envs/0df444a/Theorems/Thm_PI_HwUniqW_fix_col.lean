-- Prove2me | Theorems.Thm_PI_HwUniqW_fix_col
-- name    : PI.HwUniqW.fix_col
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:45.175694+00:00
-- url     : https://prove2.me/theorems/b7fb7fa4-8d94-4cdc-8f85-c71b51174508
-- title:
--   Hw Uniq W: fix col
-- statement:
--   The Hw Uniq W construction uses the fix col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/UnitaryOfBlockWMem.lean#L253-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/UnitaryOfBlockWMem.lean#L253-L280

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_UnitaryOfBlockWMem
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

theorem PI.HwUniqW.fix_col {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hm : FixEW k r m)
    (j : Fin (2 * r + k + 1)) (hj : ¬ InB k r j) (i : Fin (2 * r + k + 1)) :
    m i j = if i = j then 1 else 0 := by sorry
