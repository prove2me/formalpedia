-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_monomialValues_nsmul_92370521b91e
-- name    : P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_monomialValues_nsmul_92370521b91e
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:39:17.426456+00:00
-- url     : https://prove2.me/theorems/3454e33f-6229-466e-9d69-a8f6729663c2
-- title:
--   P2 M Ground Theory Heights  Heights Spanning At Dominant Weight monomial Values nsmul 92370521b91e: P2 M Ground Theory Heights  Heights Spanning At Dominant Weight monomial Values nsmul 92370521b91e
-- statement:
--   The P2 M Ground Theory Heights  Heights Spanning At Dominant Weight monomial Values nsmul 92370521b91e construction uses the P2 M Ground Theory Heights  Heights Spanning At Dominant Weight monomial Values nsmul 92370521b91e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/MonomialValuesOneBlock.lean#L112-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/MonomialValuesOneBlock.lean#L112-L116

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

theorem P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_monomialValues_nsmul_92370521b91e {Ω : Type} [Field Ω] (y : Coord n → Ω) (d : ι → ℕ) (τ : ℕ) :
    monomialValues y (τ • d) = monomialValues y d ^ τ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SpanningAtDominantWeight».«monomialValues_nsmul» := P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_monomialValues_nsmul_92370521b91e
