-- Prove2me | Theorems.Thm_PI_HwUniqW_unitary_of_blockW_mem
-- name    : PI.HwUniqW.unitary_of_blockW_mem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:07:55.521315+00:00
-- url     : https://prove2.me/theorems/a342ce54-9649-4830-a1c0-c847ea2a62d9
-- title:
--   Hw Uniq W: unitary of block W mem
-- statement:
--   The Hw Uniq W construction uses the unitary of block W mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/UnitaryOfBlockWMem.lean#L228-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/UnitaryOfBlockWMem.lean#L228-L240

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

theorem PI.HwUniqW.unitary_of_blockW_mem {h : Matrix (Fin k) (Fin k) ℂ} (hm : blockW k r h ∈ UH (Hpk k r)) :
    hᴴ * h = 1 := by sorry
