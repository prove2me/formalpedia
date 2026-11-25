-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_monomialValues_add_7ddf77459fd7
-- name    : P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_monomialValues_add_7ddf77459fd7
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:38:23.17389+00:00
-- url     : https://prove2.me/theorems/7ed96262-7f2a-429a-9484-9c150ec9716f
-- title:
--   P2 M Ground Theory Heights  Heights Spanning At Dominant Weight monomial Values add 7ddf77459fd7: P2 M Ground Theory Heights  Heights Spanning At Dominant Weight monomial Values add 7ddf77459fd7
-- statement:
--   The P2 M Ground Theory Heights  Heights Spanning At Dominant Weight monomial Values add 7ddf77459fd7 construction uses the P2 M Ground Theory Heights  Heights Spanning At Dominant Weight monomial Values add 7ddf77459fd7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/MonomialValuesOneBlock.lean#L101-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/MonomialValuesOneBlock.lean#L101-L110

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

theorem P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_monomialValues_add_7ddf77459fd7 {Ω : Type} [Field Ω] (y : Coord n → Ω) (d e : ι → ℕ) :
    monomialValues y (d + e) = monomialValues y d * monomialValues y e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SpanningAtDominantWeight».«monomialValues_add» := P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_monomialValues_add_7ddf77459fd7
