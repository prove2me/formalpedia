-- Prove2me | Theorems.Thm_PI_HwUniqW_blockW_bl
-- name    : PI.HwUniqW.blockW_bl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:22.09286+00:00
-- url     : https://prove2.me/theorems/25048a34-ab9a-4747-bb3b-14f15d96208d
-- title:
--   Hw Uniq W: block W bl
-- statement:
--   The Hw Uniq W construction uses the block W bl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/UnitaryOfBlockWMem.lean#L72-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/UnitaryOfBlockWMem.lean#L72-L75

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

theorem PI.HwUniqW.blockW_bl (h : Matrix (Fin k) (Fin k) ℂ) (a b : Fin k) :
    blockW k r h (bl k r a) (bl k r b) = h a b := by sorry
