-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_im_pi_inv
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.im_pi_inv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:34:58.798267+00:00
-- url     : https://prove2.me/theorems/27f2fcd0-184b-57c0-b1d7-e9c25d661df9
-- title:
--   Unimod Loc Std: im pi inv
-- statement:
--   The Unimod Loc Std construction uses the im pi inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/HNsmulNsmul.lean#L81-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/HNsmulNsmul.lean#L81-L100

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepSingleSat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_DescentStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_HNsmulNsmul
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
  (m : Type) [Fintype m] [DecidableEq m]
variable {a b c d ha hd lam hlam m}

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.im_pi_inv (n c₂ : ℤ) :
    ((2 * cmTheta b d - b)⁻¹ * (repKappa a b d ha hd lam hlam * ((n : ℂ) - c₂ * conj (cmTheta b d)))).im =
      -((2 * n - c₂ * b : ℤ) : ℝ) / d := by sorry
