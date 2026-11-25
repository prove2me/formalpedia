-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_chartTheta_apply
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.chartTheta_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:55:08.904533+00:00
-- url     : https://prove2.me/theorems/36599533-3c17-41b8-b576-3891f95b7fb6
-- title:
--   I1: chart Theta apply
-- statement:
--   The I1 construction uses the chart Theta apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CurvePt.lean#L114-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CurvePt.lean#L114-L116

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

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.chartTheta_apply (g : MRingOver F ι) :
    chartTheta W g = algebraMap (MRingOver F ι ⧸ W) (FractionRing (MRingOver F ι ⧸ W))
      (Ideal.Quotient.mk W g) := by sorry
