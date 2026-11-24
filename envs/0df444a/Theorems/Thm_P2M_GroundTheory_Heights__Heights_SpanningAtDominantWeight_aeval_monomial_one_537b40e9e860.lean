-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_aeval_monomial_one_537b40e9e860
-- name    : P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_aeval_monomial_one_537b40e9e860
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:08.720262+00:00
-- url     : https://prove2.me/theorems/7b6d3135-99a7-4d72-ac09-89960988f36e
-- title:
--   P2 M Ground Theory Heights  Heights Spanning At Dominant Weight aeval monomial one 537b40e9e860: P2 M Ground Theory Heights  Heights Spanning At Dominant Weight aeval monomial one 537b40e9e860
-- statement:
--   The P2 M Ground Theory Heights  Heights Spanning At Dominant Weight aeval monomial one 537b40e9e860 construction uses the P2 M Ground Theory Heights  Heights Spanning At Dominant Weight aeval monomial one 537b40e9e860 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/MonomialValuesOneBlock.lean#L71-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/MonomialValuesOneBlock.lean#L71-L73

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

theorem P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_aeval_monomial_one_537b40e9e860 {R : Type} [CommRing R] (z : Coord n → R) (μ : Coord n →₀ ℕ) :
    aeval z (monomial μ (1 : ℤ)) = ∏ p, z p ^ μ p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SpanningAtDominantWeight».«aeval_monomial_one» := P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_aeval_monomial_one_537b40e9e860
