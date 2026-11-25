-- Prove2me | Theorems.Thm_PI_OpWords_coeff_term
-- name    : PI.OpWords.coeff_term
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:17:08.395674+00:00
-- url     : https://prove2.me/theorems/597732a3-4afb-4bfd-a49d-1fe9e1bc4ff4
-- title:
--   Op Words: coeff term
-- statement:
--   The Op Words construction uses the coeff term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaCoeff.lean#L55-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaCoeff.lean#L55-L66

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

theorem PI.OpWords.coeff_term (P : MvPolynomial (Fin k) K) (m g g' : Fin k →₀ ℕ) :
    coeff (Finsupp.sumElim m g) (rename Sum.inl P * monomial (g'.mapDomain Sum.inr) (1 : K)) =
      if g' = g then coeff m P else 0 := by sorry
