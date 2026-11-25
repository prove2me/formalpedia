-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PlaceCentredSum_sum_fibre_6093e33d2f1f
-- name    : P2M_GroundTheory_Heights__Heights_PlaceCentredSum_sum_fibre_6093e33d2f1f
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:15:55.682111+00:00
-- url     : https://prove2.me/theorems/b0703037-b3ea-405c-bca0-6ede4fcba41e
-- title:
--   P2 M Ground Theory Heights  Heights Place Centred Sum sum fibre 6093e33d2f1f: P2 M Ground Theory Heights  Heights Place Centred Sum sum fibre 6093e33d2f1f
-- statement:
--   The P2 M Ground Theory Heights  Heights Place Centred Sum sum fibre 6093e33d2f1f construction uses the P2 M Ground Theory Heights  Heights Place Centred Sum sum fibre 6093e33d2f1f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PPlaceCentredSum.lean#L83-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PPlaceCentredSum.lean#L83-L88

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

theorem P2M_GroundTheory_Heights__Heights_PlaceCentredSum_sum_fibre_6093e33d2f1f (Q : HeightOneSpectrum (𝓞 L)) :
    ∑ v : {v : FinitePlace K // below v = Q}, deg L v.1 = Module.finrank L K := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PlaceCentredSum».«sum_fibre» := P2M_GroundTheory_Heights__Heights_PlaceCentredSum_sum_fibre_6093e33d2f1f
