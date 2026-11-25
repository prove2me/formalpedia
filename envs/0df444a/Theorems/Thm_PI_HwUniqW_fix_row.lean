-- Prove2me | Theorems.Thm_PI_HwUniqW_fix_row
-- name    : PI.HwUniqW.fix_row
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:09:44.887876+00:00
-- url     : https://prove2.me/theorems/6780ea47-ee22-432d-b36f-519b68965093
-- title:
--   Hw Uniq W: fix row
-- statement:
--   The Hw Uniq W construction uses the fix row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/UnitaryOfBlockWMem.lean#L288-L303
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/UnitaryOfBlockWMem.lean#L288-L303

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

theorem PI.HwUniqW.fix_row {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hU : m ∈ UH (Hpk k r))
    (hm : FixEW k r m) (i j : Fin (2 * r + k + 1)) (hi : ¬ InB k r i) (hj : InB k r j) : m i j = 0 := by sorry
