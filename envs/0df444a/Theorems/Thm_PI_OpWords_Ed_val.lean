-- Prove2me | Theorems.Thm_PI_OpWords_Ed_val
-- name    : PI.OpWords.Ed_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:35:23.146785+00:00
-- url     : https://prove2.me/theorems/351fd94f-bea6-4a27-a40f-d1340a3308fd
-- title:
--   Op Words: Ed val
-- statement:
--   The Op Words construction uses the Ed val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaCoeff.lean#L159-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaCoeff.lean#L159-L161

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

theorem PI.OpWords.Ed_val (a b : Fin k) (F : ↥(homogeneousSubmodule (Fin k) K d)) :
    (Formalism.MainNotions.TestSideCounting.Ed K k d a b F : MvPolynomial (Fin k) K) = X a * pderiv b (F : MvPolynomial (Fin k) K) := by sorry
