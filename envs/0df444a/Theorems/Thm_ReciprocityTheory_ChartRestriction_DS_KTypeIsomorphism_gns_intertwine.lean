-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_KTypeIsomorphism_gns_intertwine
-- name    : ReciprocityTheory.ChartRestriction.DS.KTypeIsomorphism.gns_intertwine
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:01:52.712637+00:00
-- url     : https://prove2.me/theorems/88659195-1618-4dc2-bca7-f68c847f2be6
-- title:
--   KType Isomorphism: gns intertwine
-- statement:
--   The KType Isomorphism construction uses the gns intertwine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/PropsEquivA.lean#L72-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/PropsEquivA.lean#L72-L100

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

theorem ReciprocityTheory.ChartRestriction.DS.KTypeIsomorphism.gns_intertwine (y₁ : ι → H₁) (y₂ : ι → H₂)
    (C₁ : Submodule ℂ H₁) (C₂ : Submodule ℂ H₂) (h₁ : ∀ i, y₁ i ∈ C₁)
    (hd₁ : C₁ ≤ (Submodule.span ℂ (Set.range y₁)).topologicalClosure)
    (U : C₁ ≃ₗᵢ[ℂ] C₂) (hU : ∀ (f : ι →₀ ℂ) (x : C₁), (x : H₁) = Finsupp.linearCombination ℂ y₁ f →
      ((U x : C₂) : H₂) = Finsupp.linearCombination ℂ y₂ f)
    (T₁ : H₁ →L[ℂ] H₁) (T₂ : H₂ →L[ℂ] H₂) (τ : ι → ι) (hT₁ : ∀ i, T₁ (y₁ i) = y₁ (τ i))
    (hT₂ : ∀ i, T₂ (y₂ i) = y₂ (τ i)) (hTC : ∀ x ∈ C₁, T₁ x ∈ C₁) :
    ∀ x y : C₁, (x : H₁) = T₁ (y : H₁) → ((U x : C₂) : H₂) = T₂ ((U y : C₂) : H₂) := by sorry
