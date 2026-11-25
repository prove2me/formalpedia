-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_chartIdeal_ne_top
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal_ne_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:08:32.415796+00:00
-- url     : https://prove2.me/theorems/8872b9bd-92e9-4da0-a5e4-e8082883d014
-- title:
--   I1: chart Ideal ne top
-- statement:
--   The I1 construction uses the chart Ideal ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CurvePt.lean#L208-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CurvePt.lean#L208-L213

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

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal_ne_top (hW : IsMultiHomogIdeal W) {j : ∀ k, ι k} (hj : IsChart W j) :
    chartIdeal W j ≠ ⊤ := by sorry
