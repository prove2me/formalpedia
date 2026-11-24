-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inhV_projVar
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.inhV_projVar
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:54:31.770811+00:00
-- url     : https://prove2.me/theorems/33152b61-2d5f-4154-b0e3-5bee6064092c
-- title:
--   I1: inh V proj Var
-- statement:
--   The I1 construction uses the inh V proj Var property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/InhDivCycleOfSuppEmpty.lean#L266-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/InhDivCycleOfSuppEmpty.lean#L266-L268

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
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
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*}
  [Field F]
variable [DecidableEq (Σ k, ι k)]

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.inhV_projVar (S : Finset (Σ k, ι k)) (d : ℕ) (h : ∀ k, ∃ i, (⟨k, i⟩ : Σ k, ι k) ∉ S)
    (hc : Nat.card {s // s ∉ S} = d + Fintype.card K) : IsProjVarF (inhV F S) d := by sorry
