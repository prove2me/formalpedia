-- Prove2me | Theorems.Thm_PI_OpWords_invFact_add_single
-- name    : PI.OpWords.invFact_add_single
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:17:09.667481+00:00
-- url     : https://prove2.me/theorems/b0ac8d93-5756-5072-afe4-e8c37199c3fa
-- title:
--   Op Words: inv Fact add single
-- statement:
--   The Op Words construction uses the inv Fact add single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaCoeff.lean#L141-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaCoeff.lean#L141-L146

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

theorem PI.OpWords.invFact_add_single [CharZero K] (g : Fin k →₀ ℕ) (i : Fin k) :
    invFact K (g + single i 1) * ((g i : K) + 1) = invFact K g := by sorry
