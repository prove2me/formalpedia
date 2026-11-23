-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_KTypeIsomorphism_dense_lcC
-- name    : ReciprocityTheory.ChartRestriction.DS.KTypeIsomorphism.dense_lcC
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:01:49.735062+00:00
-- url     : https://prove2.me/theorems/036ff174-9c7b-4346-991a-d281c1375eb8
-- title:
--   KType Isomorphism: dense lc C
-- statement:
--   The KType Isomorphism construction uses the dense lc C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/PropsEquivA.lean#L37-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/PropsEquivA.lean#L37-L46

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

theorem ReciprocityTheory.ChartRestriction.DS.KTypeIsomorphism.dense_lcC (y₁ : ι → H₁) (C₁ : Submodule ℂ H₁) (h₁ : ∀ i, y₁ i ∈ C₁)
    (hd₁ : C₁ ≤ (Submodule.span ℂ (Set.range y₁)).topologicalClosure) : DenseRange (lcC y₁ C₁ h₁) := by sorry
