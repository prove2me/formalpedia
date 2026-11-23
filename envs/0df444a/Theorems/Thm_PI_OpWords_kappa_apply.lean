-- Prove2me | Theorems.Thm_PI_OpWords_kappa_apply
-- name    : PI.OpWords.kappa_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:35:23.266149+00:00
-- url     : https://prove2.me/theorems/813dfbe4-190e-44d5-992c-83d1cb30fd7c
-- title:
--   Op Words: kappa apply
-- statement:
--   The Op Words construction uses the kappa apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaCoeff.lean#L78-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaCoeff.lean#L78-L82

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

theorem PI.OpWords.kappa_apply (A : Module.End K ↥(homogeneousSubmodule (Fin k) K d)) :
    kappa K k d A = ∑ g ∈ (Finset.univ : Finset (Fin k)).finsuppAntidiag d,
      invFact K g • (rename Sum.inl ((A (mono K k d g) : MvPolynomial (Fin k) K)) *
        monomial (g.mapDomain Sum.inr) (1 : K)) := by sorry
