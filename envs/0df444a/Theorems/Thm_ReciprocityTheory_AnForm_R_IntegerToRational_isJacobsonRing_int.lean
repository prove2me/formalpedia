-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_isJacobsonRing_int
-- name    : ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:50:21.869659+00:00
-- url     : https://prove2.me/theorems/a3acf044-452a-48d6-b5dc-0be371ad972e
-- title:
--   Integer To Rational: is Jacobson Ring int
-- statement:
--   The Integer To Rational construction uses the is Jacobson Ring int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/IntToRatA.lean#L53-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/IntToRatA.lean#L53-L66

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IntegerToRational
open MvPolynomial
variable {σ : Type} [Fintype σ]
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int : IsJacobsonRing ℤ := by sorry
