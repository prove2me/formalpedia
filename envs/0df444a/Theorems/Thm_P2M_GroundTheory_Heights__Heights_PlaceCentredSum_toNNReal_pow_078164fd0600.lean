-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PlaceCentredSum_toNNReal_pow_078164fd0600
-- name    : P2M_GroundTheory_Heights__Heights_PlaceCentredSum_toNNReal_pow_078164fd0600
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:15:49.91303+00:00
-- url     : https://prove2.me/theorems/27289a56-abe5-4b60-8eb7-66945a583d5f
-- title:
--   P2 M Ground Theory Heights  Heights Place Centred Sum to NNReal pow 078164fd0600: P2 M Ground Theory Heights  Heights Place Centred Sum to NNReal pow 078164fd0600
-- statement:
--   The P2 M Ground Theory Heights  Heights Place Centred Sum to NNReal pow 078164fd0600 construction uses the P2 M Ground Theory Heights  Heights Place Centred Sum to NNReal pow 078164fd0600 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PPlaceCentredSum.lean#L25-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PPlaceCentredSum.lean#L25-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightPlaceCentredSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PPlaceCentredSum
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
open NumberField IsDedekindDomain Ideal
open GroundTheory.Heights₂.Heights.PlaceCentredSum
variable {L K : Type} [Field L] [NumberField L] [Field K] [NumberField K] [Algebra L K]

theorem P2M_GroundTheory_Heights__Heights_PlaceCentredSum_toNNReal_pow_078164fd0600 {b c : NNReal} (hc : c ≠ 0) (hb : b ≠ 0) {f : ℕ} (hf : f ≠ 0) (h : c = b ^ f)
    (z : WithZero (Multiplicative ℤ)) :
    WithZeroMulInt.toNNReal hc z = WithZeroMulInt.toNNReal hb z ^ f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PlaceCentredSum».«toNNReal_pow» := P2M_GroundTheory_Heights__Heights_PlaceCentredSum_toNNReal_pow_078164fd0600
