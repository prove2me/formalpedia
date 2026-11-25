-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_exists_le_sum_eq_60ecb16347c3
-- name    : P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_exists_le_sum_eq_60ecb16347c3
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:39:02.079031+00:00
-- url     : https://prove2.me/theorems/37fe9a35-8195-4a39-8085-9c20b135ca33
-- title:
--   P2 M Ground Theory Heights  Heights Spanning At Dominant Weight exists le sum eq 60ecb16347c3: P2 M Ground Theory Heights  Heights Spanning At Dominant Weight exists le sum eq 60ecb16347c3
-- statement:
--   The P2 M Ground Theory Heights  Heights Spanning At Dominant Weight exists le sum eq 60ecb16347c3 construction uses the P2 M Ground Theory Heights  Heights Spanning At Dominant Weight exists le sum eq 60ecb16347c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/MonomialValuesOneBlock.lean#L15-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/MonomialValuesOneBlock.lean#L15-L39

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

theorem P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_exists_le_sum_eq_60ecb16347c3 {α : Type} [Fintype α] (f : α → ℕ) :
    ∀ a : ℕ, a ≤ ∑ i, f i → ∃ g : α → ℕ, g ≤ f ∧ ∑ i, g i = a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SpanningAtDominantWeight».«exists_le_sum_eq» := P2M_GroundTheory_Heights__Heights_SpanningAtDominantWeight_exists_le_sum_eq_60ecb16347c3
