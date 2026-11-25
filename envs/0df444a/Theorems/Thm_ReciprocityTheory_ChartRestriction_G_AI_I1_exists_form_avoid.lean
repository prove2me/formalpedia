-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_exists_form_avoid
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I1.exists_form_avoid
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:54:26.897648+00:00
-- url     : https://prove2.me/theorems/549f5d84-09ac-5be7-b4d9-a18ec8686b79
-- title:
--   I1: exists form avoid
-- statement:
--   The I1 construction uses the exists form avoid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/ExistsMonomialNotMem.lean#L108-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/ExistsMonomialNotMem.lean#L108-L182

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsMonomialNotMem
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

theorem ReciprocityTheory.ChartRestriction.G.AI.I1.exists_form_avoid (S : Set (Ideal (MRingOver F ι))) (hS : S.Finite)
    (hS' : ∀ W ∈ S, IsMultiProjPrime W) :
    ∃ d₀ : K → ℕ, ∀ d : K → ℕ, d₀ ≤ d →
      ∃ f : MRingOver F ι, IsMultiHomog f d ∧ ∀ W ∈ S, f ∉ W := by sorry
