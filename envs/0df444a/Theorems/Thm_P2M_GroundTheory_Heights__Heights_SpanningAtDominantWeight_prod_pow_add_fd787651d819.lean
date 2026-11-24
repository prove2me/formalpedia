-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_prod_pow_add_fd787651d819
-- name    : P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_prod_pow_add_fd787651d819
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:19.958811+00:00
-- url     : https://prove2.me/theorems/2d0767b8-117b-4ecb-834c-ebacd4aca1d9
-- title:
--   P2 M Ground Theory Heights  Heights Spanning At Dominant Weight prod pow add fd787651d819: P2 M Ground Theory Heights  Heights Spanning At Dominant Weight prod pow add fd787651d819
-- statement:
--   The P2 M Ground Theory Heights  Heights Spanning At Dominant Weight prod pow add fd787651d819 construction uses the P2 M Ground Theory Heights  Heights Spanning At Dominant Weight prod pow add fd787651d819 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/MonomialValuesOneBlock.lean#L67-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/MonomialValuesOneBlock.lean#L67-L69

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

theorem P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_prod_pow_add_fd787651d819 {M : Type} [CommMonoid M] (z : Coord n → M) (μ₁ μ₂ : Coord n →₀ ℕ) :
    ∏ p, z p ^ (μ₁ + μ₂) p = (∏ p, z p ^ μ₁ p) * ∏ p, z p ^ μ₂ p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SpanningAtDominantWeight».«prod_pow_add» := P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_prod_pow_add_fd787651d819
