-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PlaceCentredSum_apply_algebraMap_fc47d50d1873
-- name    : P2M_GroundTheory_Heights__Heights_PlaceCentredSum_apply_algebraMap_fc47d50d1873
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:55.87765+00:00
-- url     : https://prove2.me/theorems/77653506-4299-4a3e-b2d3-1c699fd8acb4
-- title:
--   P2 M Ground Theory Heights  Heights Place Centred Sum apply algebra Map fc47d50d1873: P2 M Ground Theory Heights  Heights Place Centred Sum apply algebra Map fc47d50d1873
-- statement:
--   The P2 M Ground Theory Heights  Heights Place Centred Sum apply algebra Map fc47d50d1873 construction uses the P2 M Ground Theory Heights  Heights Place Centred Sum apply algebra Map fc47d50d1873 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PPlaceCentredSum.lean#L34-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PPlaceCentredSum.lean#L34-L46

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

theorem P2M_GroundTheory_Heights__Heights_PlaceCentredSum_apply_algebraMap_fc47d50d1873 (v : FinitePlace K) (x : L) :
    v (algebraMap L K x) = FinitePlace.mk (below v) x ^ deg L v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PlaceCentredSum».«apply_algebraMap» := P2M_GroundTheory_Heights__Heights_PlaceCentredSum_apply_algebraMap_fc47d50d1873
