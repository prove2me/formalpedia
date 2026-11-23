-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_disj_intS
-- name    : ReciprocityTheory.AnForm.R.IntegerToRational.disj_intS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:59:29.485088+00:00
-- url     : https://prove2.me/theorems/7a9ea442-ef9d-43a9-8759-96bb2d25a8e1
-- title:
--   Integer To Rational: disj int S
-- statement:
--   The Integer To Rational construction uses the disj int S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/IntToRatA.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/IntToRatA.lean#L16-L20

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

theorem ReciprocityTheory.AnForm.R.IntegerToRational.disj_intS (P : Ideal (MvPolynomial σ ℤ)) (hP : ChZero P) :
    Disjoint ((intS σ : Submonoid _) : Set (MvPolynomial σ ℤ)) (P : Set _) := by sorry
