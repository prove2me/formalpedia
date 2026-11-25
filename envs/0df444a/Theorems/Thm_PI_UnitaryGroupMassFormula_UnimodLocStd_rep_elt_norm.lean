-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_elt_norm
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.rep_elt_norm
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:41:19.520824+00:00
-- url     : https://prove2.me/theorems/8e1f485e-08e2-4ff7-8a97-9ec76005f196
-- title:
--   Unimod Loc Std: rep elt norm
-- statement:
--   The Unimod Loc Std construction uses the rep elt norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/RepArith.lean#L34-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/RepArith.lean#L34-L43

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

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.rep_elt_norm (hOK : 4 * (a : ℤ) * c = b ^ 2 + d) (p q : ℤ) :
    (lam * ((p : ℂ) * a + q * cmTheta b d)) * conj (lam * ((p : ℂ) * a + q * cmTheta b d)) =
      (Complex.normSq lam : ℂ) * a * ((a * p ^ 2 + b * p * q + c * q ^ 2 : ℤ) : ℂ) := by sorry
