-- Prove2me | Theorems.Thm_PI_OpWords_degree_of_coeff_ne
-- name    : PI.OpWords.degree_of_coeff_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:35:32.676277+00:00
-- url     : https://prove2.me/theorems/e060af3a-3bbb-4aed-8ebb-0a842034b7dd
-- title:
--   Op Words: degree of coeff ne
-- statement:
--   The Op Words construction uses the degree of coeff ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaCoeff.lean#L99-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaCoeff.lean#L99-L103

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

theorem PI.OpWords.degree_of_coeff_ne (F : ↥(homogeneousSubmodule (Fin k) K d)) {m : Fin k →₀ ℕ}
    (h : coeff m (F : MvPolynomial (Fin k) K) ≠ 0) : m.degree = d := by sorry
