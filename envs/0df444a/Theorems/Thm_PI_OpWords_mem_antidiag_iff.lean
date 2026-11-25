-- Prove2me | Theorems.Thm_PI_OpWords_mem_antidiag_iff
-- name    : PI.OpWords.mem_antidiag_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:35:53.924107+00:00
-- url     : https://prove2.me/theorems/26a84b5f-3105-45e2-9554-5fca17450930
-- title:
--   Op Words: mem antidiag iff
-- statement:
--   The Op Words construction uses the mem antidiag iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaCoeff.lean#L73-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaCoeff.lean#L73-L76

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

theorem PI.OpWords.mem_antidiag_iff (g : Fin k →₀ ℕ) :
    g ∈ (Finset.univ : Finset (Fin k)).finsuppAntidiag d ↔ g.degree = d := by sorry
