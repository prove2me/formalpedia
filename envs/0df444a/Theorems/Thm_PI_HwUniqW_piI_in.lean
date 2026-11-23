-- Prove2me | Theorems.Thm_PI_HwUniqW_piI_in
-- name    : PI.HwUniqW.piI_in
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:57.095295+00:00
-- url     : https://prove2.me/theorems/be95df58-6f56-43b0-83be-fd9634ce06ca
-- title:
--   Hw Uniq W: pi I in
-- statement:
--   The Hw Uniq W construction uses the pi I in property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/UnitaryOfBlockWMem.lean#L153-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/UnitaryOfBlockWMem.lean#L153-L156

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

theorem PI.HwUniqW.piI_in {i : Fin (2 * r + k + 1)} (hi : InB k r i) : piI k r i = i := by sorry
