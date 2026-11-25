-- Prove2me | Theorems.Thm_PI_OpWords_eq_sum_mono
-- name    : PI.OpWords.eq_sum_mono
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:17:39.548164+00:00
-- url     : https://prove2.me/theorems/0a374c17-d18f-52e0-a4c6-c3feef47a8f3
-- title:
--   Op Words: eq sum mono
-- statement:
--   The Op Words construction uses the eq sum mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaCoeff.lean#L105-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaCoeff.lean#L105-L113

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

theorem PI.OpWords.eq_sum_mono (F : ↥(homogeneousSubmodule (Fin k) K d)) :
    F = ∑ g ∈ (F : MvPolynomial (Fin k) K).support,
      coeff g (F : MvPolynomial (Fin k) K) • mono K k d g := by sorry
