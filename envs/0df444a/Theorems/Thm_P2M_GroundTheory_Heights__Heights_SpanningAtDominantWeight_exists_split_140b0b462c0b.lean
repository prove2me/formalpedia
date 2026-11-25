-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_exists_split_140b0b462c0b
-- name    : P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_exists_split_140b0b462c0b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:15.242893+00:00
-- url     : https://prove2.me/theorems/a7109b06-afbd-4051-8b7e-52793dba87e2
-- title:
--   P2 M Ground Theory Heights  Heights Spanning At Dominant Weight exists split 140b0b462c0b: P2 M Ground Theory Heights  Heights Spanning At Dominant Weight exists split 140b0b462c0b
-- statement:
--   The P2 M Ground Theory Heights  Heights Spanning At Dominant Weight exists split 140b0b462c0b construction uses the P2 M Ground Theory Heights  Heights Spanning At Dominant Weight exists split 140b0b462c0b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/MonomialValuesOneBlock.lean#L43-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/MonomialValuesOneBlock.lean#L43-L65

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_MonomialValuesOneBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
open scoped Pointwise
noncomputable section
open GroundTheory.Heights₂.Heights.SpanningAtDominantWeight
variable {ι : Type} [Fintype ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_exists_split_140b0b462c0b (μ : Coord n →₀ ℕ) (d e : ι → ℕ) (hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = d k + e k) :
    ∃ μ₁ μ₂ : Coord n →₀ ℕ, μ = μ₁ + μ₂ ∧ (∀ k, ∑ i, μ₁ ⟨k, i⟩ = d k) ∧ ∀ k, ∑ i, μ₂ ⟨k, i⟩ = e k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SpanningAtDominantWeight».«exists_split» := P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_exists_split_140b0b462c0b
