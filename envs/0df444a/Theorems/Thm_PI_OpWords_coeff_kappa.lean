-- Prove2me | Theorems.Thm_PI_OpWords_coeff_kappa
-- name    : PI.OpWords.coeff_kappa
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:15:42.899749+00:00
-- url     : https://prove2.me/theorems/f85681a8-3a8c-4930-aed2-9c571dfb2033
-- title:
--   Op Words: coeff kappa
-- statement:
--   The Op Words construction uses the coeff kappa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaCoeff.lean#L84-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaCoeff.lean#L84-L97

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

theorem PI.OpWords.coeff_kappa (A : Module.End K ↥(homogeneousSubmodule (Fin k) K d)) (m g : Fin k →₀ ℕ) :
    coeff (Finsupp.sumElim m g) (kappa K k d A) =
      invFact K g * coeff m (A (mono K k d g) : MvPolynomial (Fin k) K) := by sorry
