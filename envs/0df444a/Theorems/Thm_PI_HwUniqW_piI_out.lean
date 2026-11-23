-- Prove2me | Theorems.Thm_PI_HwUniqW_piI_out
-- name    : PI.HwUniqW.piI_out
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:26.998225+00:00
-- url     : https://prove2.me/theorems/e7a212c0-baaf-43ee-b530-64e2ec8cf7f9
-- title:
--   Hw Uniq W: pi I out
-- statement:
--   The Hw Uniq W construction uses the pi I out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/UnitaryOfBlockWMem.lean#L163-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/UnitaryOfBlockWMem.lean#L163-L170

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

theorem PI.HwUniqW.piI_out {i : Fin (2 * r + k + 1)} (hi : ¬ InB k r i) : ¬ InB k r (piI k r i) := by sorry
