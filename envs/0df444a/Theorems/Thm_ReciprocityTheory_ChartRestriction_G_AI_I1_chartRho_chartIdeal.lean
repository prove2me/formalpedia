-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_chartRho_chartIdeal
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.chartRho_chartIdeal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:08:45.158481+00:00
-- url     : https://prove2.me/theorems/bd8c8b7d-0601-499e-8c09-c29ae9cb4553
-- title:
--   I1: chart Rho chart Ideal
-- statement:
--   The I1 construction uses the chart Rho chart Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CurvePt.lean#L159-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CurvePt.lean#L159-L188

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
variable {W : Ideal (MRingOver F ι)} [hWp : W.IsPrime]

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.chartRho_chartIdeal (hW : IsMultiHomogIdeal W) {j : ∀ k, ι k} (hj : IsChart W j)
    {g : MRingOver F ι} (hg : g ∈ chartIdeal W j) : chartRho W j g = 0 := by sorry
