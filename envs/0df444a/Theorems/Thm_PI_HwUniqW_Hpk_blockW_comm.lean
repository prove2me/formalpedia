-- Prove2me | Theorems.Thm_PI_HwUniqW_Hpk_blockW_comm
-- name    : PI.HwUniqW.Hpk_blockW_comm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:12.023587+00:00
-- url     : https://prove2.me/theorems/3fbc2b8e-08c6-4872-9401-720c7bd635d6
-- title:
--   Hw Uniq W: Hpk block W comm
-- statement:
--   The Hw Uniq W construction uses the Hpk block W comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/UnitaryOfBlockWMem.lean#L204-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/UnitaryOfBlockWMem.lean#L204-L218

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

theorem PI.HwUniqW.Hpk_blockW_comm (a : Matrix (Fin k) (Fin k) ℂ) :
    Hpk k r * blockW k r a = blockW k r a * Hpk k r := by sorry
