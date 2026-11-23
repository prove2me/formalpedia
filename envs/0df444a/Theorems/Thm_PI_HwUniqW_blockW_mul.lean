-- Prove2me | Theorems.Thm_PI_HwUniqW_blockW_mul
-- name    : PI.HwUniqW.blockW_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:46:12.572331+00:00
-- url     : https://prove2.me/theorems/9517d6ef-fed7-40d3-b054-14438241de57
-- title:
--   Hw Uniq W: block W mul
-- statement:
--   The Hw Uniq W construction uses the block W mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/UnitaryOfBlockWMem.lean#L81-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/UnitaryOfBlockWMem.lean#L81-L119

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

theorem PI.HwUniqW.blockW_mul (a b : Matrix (Fin k) (Fin k) ℂ) :
    blockW k r a * blockW k r b = blockW k r (a * b) := by sorry
