-- Prove2me | Theorems.Thm_PI_HwUniqW_fix_block
-- name    : PI.HwUniqW.fix_block
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:45.202273+00:00
-- url     : https://prove2.me/theorems/a6dfd491-00fd-485f-b4bc-04d55c6746d0
-- title:
--   Hw Uniq W: fix block
-- statement:
--   The Hw Uniq W construction uses the fix block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/UnitaryOfBlockWMem.lean#L305-L322
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/UnitaryOfBlockWMem.lean#L305-L322

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

theorem PI.HwUniqW.fix_block {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hU : m ∈ UH (Hpk k r))
    (hm : FixEW k r m) : sub k r m ∈ UJset (allPos k) ∧ m = blockW k r (sub k r m) := by sorry
