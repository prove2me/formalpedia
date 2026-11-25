-- Prove2me | Theorems.Thm_PI_OpWords_weight_wxi
-- name    : PI.OpWords.weight_wxi
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:16:29.850217+00:00
-- url     : https://prove2.me/theorems/77e85eb0-dca2-4ef2-a186-529b714e5649
-- title:
--   Op Words: weight wxi
-- statement:
--   The Op Words construction uses the weight wxi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaCoeff.lean#L183-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaCoeff.lean#L183-L184

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaCoeff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finsupp
noncomputable section
open PI PI.OpWords
variable {K : Type} [Field K] {k d : ℕ}

theorem PI.OpWords.weight_wxi (m g : Fin k →₀ ℕ) : Finsupp.weight (wxi k) (Finsupp.sumElim m g) = g.degree := by sorry
