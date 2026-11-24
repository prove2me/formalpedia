-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isUnit_mk_chartIdeal_form
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.isUnit_mk_chartIdeal_form
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:24:20.813802+00:00
-- url     : https://prove2.me/theorems/101247b4-0a75-4819-af42-5ba0e03618e3
-- title:
--   I1: is Unit mk chart Ideal form
-- statement:
--   The I1 construction uses the is Unit mk chart Ideal form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CurvePt.lean#L221-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CurvePt.lean#L221-L312

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsMonomialNotMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]
variable {W : Ideal (MRingOver F ι)}

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.isUnit_mk_chartIdeal_form {V : Ideal (MRingOver F ι)} (hV : IsProjVarF V 0) (j : ∀ k, ι k)
    {a : MRingOver F ι} {α : K → ℕ} (ha : IsMultiHomog a α) (hp : a ∉ V) :
    IsUnit (Ideal.Quotient.mk (chartIdeal V j) a) := by sorry
