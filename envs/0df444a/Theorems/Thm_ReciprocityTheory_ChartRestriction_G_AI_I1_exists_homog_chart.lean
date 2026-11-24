-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_exists_homog_chart
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.exists_homog_chart
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:08:36.70995+00:00
-- url     : https://prove2.me/theorems/4f170fa9-8905-42c6-96b5-1347f49830d6
-- title:
--   I1: exists homog chart
-- statement:
--   The I1 construction uses the exists homog chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CurvePt.lean#L59-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CurvePt.lean#L59-L101

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
variable [DecidableEq K]
attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.exists_homog_chart (V : Ideal (MRingOver F ι)) (j : ∀ k, ι k) (b : MRingOver F ι) :
    ∃ e₀ : K → ℕ, ∀ e, e₀ ≤ e → ∃ b' ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) e,
      Ideal.Quotient.mk (chartIdeal V j) b' = Ideal.Quotient.mk (chartIdeal V j) b := by sorry
