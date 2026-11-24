-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_theta_mul_conj
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.rep_theta_mul_conj
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:04:51.924169+00:00
-- url     : https://prove2.me/theorems/8a6a8dc4-9456-4676-9192-374ff05cb549
-- title:
--   Unimod Loc Std: rep theta mul conj
-- statement:
--   The Unimod Loc Std construction uses the rep theta mul conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/RepArith.lean#L25-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/RepArith.lean#L25-L32

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepArith
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
variable (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.rep_theta_mul_conj (hOK : 4 * (a : ℤ) * c = b ^ 2 + d) :
    cmTheta b d * conj (cmTheta b d) = (a : ℂ) * c := by sorry
