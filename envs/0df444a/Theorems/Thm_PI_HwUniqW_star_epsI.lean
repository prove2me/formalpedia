-- Prove2me | Theorems.Thm_PI_HwUniqW_star_epsI
-- name    : PI.HwUniqW.star_epsI
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:07:45.846118+00:00
-- url     : https://prove2.me/theorems/36425724-579e-5ef6-84bb-56dea7332c7b
-- title:
--   Hw Uniq W: star eps I
-- statement:
--   The Hw Uniq W construction uses the star eps I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/HpkMulMulHpkApply.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/HpkMulMulHpkApply.lean#L38-L40

import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
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

theorem PI.HwUniqW.star_epsI (i : Fin (2 * r + k + 1)) : star (epsI k r i) = epsI k r i := by sorry
