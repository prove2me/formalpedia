-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_chartTheta_X_ne_zero
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.chartTheta_X_ne_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:08:31.989447+00:00
-- url     : https://prove2.me/theorems/0db71472-a19d-4e1d-927a-60c526c79124
-- title:
--   I1: chart Theta X ne zero
-- statement:
--   The I1 construction uses the chart Theta X ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CurvePt.lean#L131-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CurvePt.lean#L131-L135

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

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.chartTheta_X_ne_zero {j : ∀ k, ι k} (hj : IsChart W j) (k : K) :
    chartTheta W (X ⟨k, j k⟩) ≠ 0 := by sorry
