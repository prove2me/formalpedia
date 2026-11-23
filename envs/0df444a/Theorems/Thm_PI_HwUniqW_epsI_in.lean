-- Prove2me | Theorems.Thm_PI_HwUniqW_epsI_in
-- name    : PI.HwUniqW.epsI_in
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:45.698728+00:00
-- url     : https://prove2.me/theorems/8adff4d2-b796-46df-864f-5bdfb6b8ed7f
-- title:
--   Hw Uniq W: eps I in
-- statement:
--   The Hw Uniq W construction uses the eps I in property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/UnitaryOfBlockWMem.lean#L158-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/UnitaryOfBlockWMem.lean#L158-L161

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

theorem PI.HwUniqW.epsI_in {i : Fin (2 * r + k + 1)} (hi : InB k r i) : epsI k r i = 1 := by sorry
