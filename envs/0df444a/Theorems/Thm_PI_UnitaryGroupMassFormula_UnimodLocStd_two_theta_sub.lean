-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_two_theta_sub
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.two_theta_sub
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:41:10.484852+00:00
-- url     : https://prove2.me/theorems/a32fd286-be76-43be-b71e-fefd039a3962
-- title:
--   Unimod Loc Std: two theta sub
-- statement:
--   The Unimod Loc Std construction uses the two theta sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/RelIdxNeZeroOfLeLeft.lean#L187-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/RelIdxNeZeroOfLeLeft.lean#L187-L192

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RelIdxNeZeroOfLeLeft
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable {a : ℕ} {b c : ℤ} {d : ℕ}

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.two_theta_sub (b : ℤ) {d : ℕ} (hd : 0 < d) : 2 * cmTheta b d - b ≠ 0 := by sorry
