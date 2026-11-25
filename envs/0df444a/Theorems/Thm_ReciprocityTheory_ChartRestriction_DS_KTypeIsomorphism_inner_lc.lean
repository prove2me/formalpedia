-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_KTypeIsomorphism_inner_lc
-- name    : ReciprocityTheory.ChartRestriction.DS.KTypeIsomorphism.inner_lc
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:41:26.385824+00:00
-- url     : https://prove2.me/theorems/f1f54677-a971-55c0-8c80-3938981a7daa
-- title:
--   KType Isomorphism: inner lc
-- statement:
--   The KType Isomorphism construction uses the inner lc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/PropsEquivA.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/PropsEquivA.lean#L16-L21

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

theorem ReciprocityTheory.ChartRestriction.DS.KTypeIsomorphism.inner_lc (y₁ : ι → H₁) (y₂ : ι → H₂)
    (hI : ∀ i j, inner ℂ (y₂ i) (y₂ j) = inner ℂ (y₁ i) (y₁ j)) (f f' : ι →₀ ℂ) :
    inner ℂ (Finsupp.linearCombination ℂ y₂ f) (Finsupp.linearCombination ℂ y₂ f') =
      inner ℂ (Finsupp.linearCombination ℂ y₁ f) (Finsupp.linearCombination ℂ y₁ f') := by sorry
