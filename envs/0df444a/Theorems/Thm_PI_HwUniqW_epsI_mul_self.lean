-- Prove2me | Theorems.Thm_PI_HwUniqW_epsI_mul_self
-- name    : PI.HwUniqW.epsI_mul_self
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:08:09.579034+00:00
-- url     : https://prove2.me/theorems/e24f0a22-5a93-43fe-9e8b-c8bbcc41c20d
-- title:
--   Hw Uniq W: eps I mul self
-- statement:
--   The Hw Uniq W construction uses the eps I mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/HpkMulMulHpkApply.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/HpkMulMulHpkApply.lean#L34-L36

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

theorem PI.HwUniqW.epsI_mul_self (i : Fin (2 * r + k + 1)) : epsI k r i * epsI k r i = 1 := by sorry
