-- Prove2me | Theorems.Thm_PI_OpWords_mapDomain_inl_add_inr
-- name    : PI.OpWords.mapDomain_inl_add_inr
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:16:29.686746+00:00
-- url     : https://prove2.me/theorems/2c1922c2-c02e-4d36-abc0-3eee6a5b7a7b
-- title:
--   Op Words: map Domain inl add inr
-- statement:
--   The Op Words construction uses the map Domain inl add inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaCoeff.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaCoeff.lean#L12-L17

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

theorem PI.OpWords.mapDomain_inl_add_inr (u g : Fin k →₀ ℕ) :
    u.mapDomain Sum.inl + g.mapDomain Sum.inr = Finsupp.sumElim u g := by sorry
