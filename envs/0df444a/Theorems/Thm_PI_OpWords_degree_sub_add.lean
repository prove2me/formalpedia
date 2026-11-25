-- Prove2me | Theorems.Thm_PI_OpWords_degree_sub_add
-- name    : PI.OpWords.degree_sub_add
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:17:02.646451+00:00
-- url     : https://prove2.me/theorems/9a54960f-aa7d-5c61-8992-961ff46245a5
-- title:
--   Op Words: degree sub add
-- statement:
--   The Op Words construction uses the degree sub add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaCoeff.lean#L148-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaCoeff.lean#L148-L157

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

theorem PI.OpWords.degree_sub_add (g : Fin k →₀ ℕ) (a b : Fin k) (hb : g b ≠ 0) :
    (g - single b 1 + single a 1).degree = g.degree := by sorry
