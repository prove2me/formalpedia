-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_mem_of_mem_chartIdeal
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.mem_of_mem_chartIdeal
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:54:55.060109+00:00
-- url     : https://prove2.me/theorems/2a526a55-244c-57c4-89b5-d52e9c4d4fd8
-- title:
--   I1: mem of mem chart Ideal
-- statement:
--   The I1 construction uses the mem of mem chart Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CurvePt.lean#L204-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CurvePt.lean#L204-L206

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

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.mem_of_mem_chartIdeal [DecidableEq K] (hW : IsMultiHomogIdeal W) {j : ∀ k, ι k}
    (hj : IsChart W j) {e : K → ℕ} {a : MRingOver F ι}
    (ha : a ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) e) (haW : a ∈ chartIdeal W j) : a ∈ W := by sorry
