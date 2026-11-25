-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_monomial_mem_weighted
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.monomial_mem_weighted
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:11:10.17386+00:00
-- url     : https://prove2.me/theorems/f217a3d8-b7b7-4e87-b291-b849f6fe3b17
-- title:
--   I1: monomial mem weighted
-- statement:
--   The I1 construction uses the monomial mem weighted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CurvePt.lean#L55-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/CurvePt.lean#L55-L57

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

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.monomial_mem_weighted (m : (Σ k, ι k) →₀ ℕ) (c : F) :
    monomial m c ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) (fun k => ∑ i, m ⟨k, i⟩) := by sorry
