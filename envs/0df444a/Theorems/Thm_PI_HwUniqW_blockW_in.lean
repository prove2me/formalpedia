-- Prove2me | Theorems.Thm_PI_HwUniqW_blockW_in
-- name    : PI.HwUniqW.blockW_in
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:40:56.237486+00:00
-- url     : https://prove2.me/theorems/2fb93544-3881-4e89-b054-609a8f526794
-- title:
--   Hw Uniq W: block W in
-- statement:
--   The Hw Uniq W construction uses the block W in property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/UnitaryOfBlockWMem.lean#L51-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/UnitaryOfBlockWMem.lean#L51-L57

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

theorem PI.HwUniqW.blockW_in (h : Matrix (Fin k) (Fin k) ℂ) {i j : Fin (2 * r + k + 1)} (hi : InB k r i)
    (hj : InB k r j) :
    blockW k r h i j = h ⟨i.val - r, by unfold InB at hi; omega⟩ ⟨j.val - r, by unfold InB at hj; omega⟩ := by sorry
