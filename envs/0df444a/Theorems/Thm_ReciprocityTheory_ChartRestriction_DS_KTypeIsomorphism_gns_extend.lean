-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_KTypeIsomorphism_gns_extend
-- name    : ReciprocityTheory.ChartRestriction.DS.KTypeIsomorphism.gns_extend
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:01:45.180726+00:00
-- url     : https://prove2.me/theorems/a02a7e94-e457-4325-a58d-5b7b03518621
-- title:
--   KType Isomorphism: gns extend
-- statement:
--   The KType Isomorphism construction uses the gns extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/PropsEquivA.lean#L50-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/PropsEquivA.lean#L50-L70

import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_PropsEquivA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
open ReciprocityTheory.ChartRestriction.DS.KTypeIsomorphism
variable {ι : Type*} {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
variable [CompleteSpace H₁] [CompleteSpace H₂]

theorem ReciprocityTheory.ChartRestriction.DS.KTypeIsomorphism.gns_extend (y₁ : ι → H₁) (y₂ : ι → H₂)
    (hI : ∀ i j, inner ℂ (y₂ i) (y₂ j) = inner ℂ (y₁ i) (y₁ j))
    (C₁ : Submodule ℂ H₁) (C₂ : Submodule ℂ H₂) (hC₁ : IsClosed (C₁ : Set H₁)) (hC₂ : IsClosed (C₂ : Set H₂))
    (h₁ : ∀ i, y₁ i ∈ C₁) (h₂ : ∀ i, y₂ i ∈ C₂)
    (hd₁ : C₁ ≤ (Submodule.span ℂ (Set.range y₁)).topologicalClosure)
    (hd₂ : C₂ ≤ (Submodule.span ℂ (Set.range y₂)).topologicalClosure) :
    ∃ U : C₁ ≃ₗᵢ[ℂ] C₂, ∀ (f : ι →₀ ℂ) (x : C₁), (x : H₁) = Finsupp.linearCombination ℂ y₁ f →
      ((U x : C₂) : H₂) = Finsupp.linearCombination ℂ y₂ f := by sorry
