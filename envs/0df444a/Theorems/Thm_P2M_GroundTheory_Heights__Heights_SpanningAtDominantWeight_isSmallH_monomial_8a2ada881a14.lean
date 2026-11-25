-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_isSmallH_monomial_8a2ada881a14
-- name    : P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_isSmallH_monomial_8a2ada881a14
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:38:36.377319+00:00
-- url     : https://prove2.me/theorems/a21702f8-5d8d-4ff7-bc57-cb72aa6c076a
-- title:
--   P2 M Ground Theory Heights  Heights Spanning At Dominant Weight is Small H monomial 8a2ada881a14: P2 M Ground Theory Heights  Heights Spanning At Dominant Weight is Small H monomial 8a2ada881a14
-- statement:
--   The P2 M Ground Theory Heights  Heights Spanning At Dominant Weight is Small H monomial 8a2ada881a14 construction uses the P2 M Ground Theory Heights  Heights Spanning At Dominant Weight is Small H monomial 8a2ada881a14 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/MonomialValuesOneBlock.lean#L160-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/MonomialValuesOneBlock.lean#L160-L185

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

theorem P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_isSmallH_monomial_8a2ada881a14 {Ω : Type} [Field Ω] (y : Coord n → Ω) (A : Geo.HermLine (blockIdx n)) (b : ι → ℕ)
    (hAa : ∀ k, A.a k = b k)
    (hA : Geo.MonomialsBounded (ι := blockIdx n) (Geo.mCoordIdeal (ι := blockIdx n) y) A b) (τ : ℕ)
    (μ : Coord n →₀ ℕ) (hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = (τ • b) k) :
    Geo.IsSmallH (ι := blockIdx n) (Geo.mCoordIdeal (ι := blockIdx n) y) y A τ (∏ p, y p ^ μ p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SpanningAtDominantWeight».«isSmallH_monomial» := P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_isSmallH_monomial_8a2ada881a14
