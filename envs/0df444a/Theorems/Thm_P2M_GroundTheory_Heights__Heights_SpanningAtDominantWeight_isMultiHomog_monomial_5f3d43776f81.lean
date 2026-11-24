-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_isMultiHomog_monomial_5f3d43776f81
-- name    : P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_isMultiHomog_monomial_5f3d43776f81
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:21.668618+00:00
-- url     : https://prove2.me/theorems/439e9e9e-caa4-4728-a314-86186239fec9
-- title:
--   P2 M Ground Theory Heights  Heights Spanning At Dominant Weight is Multi Homog monomial 5f3d43776f81: P2 M Ground Theory Heights  Heights Spanning At Dominant Weight is Multi Homog monomial 5f3d43776f
-- statement:
--   The P2 M Ground Theory Heights  Heights Spanning At Dominant Weight is Multi Homog monomial 5f3d43776f81 construction uses the P2 M Ground Theory Heights  Heights Spanning At Dominant Weight is Multi Homog monomial 5f3d43776f81 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/MonomialValuesOneBlock.lean#L77-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/MonomialValuesOneBlock.lean#L77-L84

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
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_isMultiHomog_monomial_5f3d43776f81 (μ : Coord n →₀ ℕ) (d : ι → ℕ) (hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = d k) :
    Geo.IsMultiHomog (ι := blockIdx n) (monomial μ (1 : ℤ)) d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SpanningAtDominantWeight».«isMultiHomog_monomial» := P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_isMultiHomog_monomial_5f3d43776f81
