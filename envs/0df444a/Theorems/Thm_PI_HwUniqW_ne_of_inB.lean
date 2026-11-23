-- Prove2me | Theorems.Thm_PI_HwUniqW_ne_of_inB
-- name    : PI.HwUniqW.ne_of_inB
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:42:35.783984+00:00
-- url     : https://prove2.me/theorems/c1ae5d7a-e8bb-45e0-ba73-62c667fe8380
-- title:
--   Hw Uniq W: ne of in B
-- statement:
--   The Hw Uniq W construction uses the ne of in B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/UnitaryOfBlockWMem.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/UnitaryOfBlockWMem.lean#L46-L49

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

theorem PI.HwUniqW.ne_of_inB {i j : Fin (2 * r + k + 1)} (hi : InB k r i) (hj : ¬ InB k r j) : i ≠ j := by sorry
