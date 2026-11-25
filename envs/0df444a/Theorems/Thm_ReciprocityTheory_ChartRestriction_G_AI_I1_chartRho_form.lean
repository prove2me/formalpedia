-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_chartRho_form
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.chartRho_form
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:55:07.013267+00:00
-- url     : https://prove2.me/theorems/0fd43df4-bf21-4310-9218-ddd3ef8aa9e3
-- title:
--   I1: chart Rho form
-- statement:
--   The I1 construction uses the chart Rho form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CurvePt.lean#L190-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CurvePt.lean#L190-L202

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

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.chartRho_form [DecidableEq K] {j : ∀ k, ι k} (hj : IsChart W j) {e : K → ℕ} {a : MRingOver F ι}
    (ha : a ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) e) (h0 : chartRho W j a = 0) : a ∈ W := by sorry
