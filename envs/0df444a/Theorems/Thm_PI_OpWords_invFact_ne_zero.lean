-- Prove2me | Theorems.Thm_PI_OpWords_invFact_ne_zero
-- name    : PI.OpWords.invFact_ne_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:24:54.789145+00:00
-- url     : https://prove2.me/theorems/582fa325-d3b4-4324-8706-a63b95794df9
-- title:
--   Op Words: inv Fact ne zero
-- statement:
--   The Op Words construction uses the inv Fact ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaCoeff.lean#L124-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaCoeff.lean#L124-L126

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

theorem PI.OpWords.invFact_ne_zero [CharZero K] (g : Fin k →₀ ℕ) : invFact K g ≠ 0 := by sorry
