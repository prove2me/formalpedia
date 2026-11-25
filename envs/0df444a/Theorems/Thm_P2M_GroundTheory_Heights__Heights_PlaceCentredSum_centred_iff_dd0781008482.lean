-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PlaceCentredSum_centred_iff_dd0781008482
-- name    : P2M_GroundTheory_Heights__Heights_PlaceCentredSum_centred_iff_dd0781008482
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:22:05.608565+00:00
-- url     : https://prove2.me/theorems/911c7352-592b-5a06-a6f9-114267b8bc7e
-- title:
--   P2 M Ground Theory Heights  Heights Place Centred Sum centred iff dd0781008482: P2 M Ground Theory Heights  Heights Place Centred Sum centred iff dd0781008482
-- statement:
--   The P2 M Ground Theory Heights  Heights Place Centred Sum centred iff dd0781008482 construction uses the P2 M Ground Theory Heights  Heights Place Centred Sum centred iff dd0781008482 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PPlaceCentredSum.lean#L53-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PPlaceCentredSum.lean#L53-L63

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

theorem P2M_GroundTheory_Heights__Heights_PlaceCentredSum_centred_iff_dd0781008482 (O : Subalgebra ℤ L) (m : Ideal O) (v : FinitePlace K) :
    AbsCentredAt O m (fun u ↦ v (algebraMap L K u)) ↔
      AbsCentredAt O m (fun u ↦ FinitePlace.mk (below v) u) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PlaceCentredSum».«centred_iff» := P2M_GroundTheory_Heights__Heights_PlaceCentredSum_centred_iff_dd0781008482
