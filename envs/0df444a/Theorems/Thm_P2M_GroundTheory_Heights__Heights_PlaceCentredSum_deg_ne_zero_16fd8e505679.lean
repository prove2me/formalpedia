-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PlaceCentredSum_deg_ne_zero_16fd8e505679
-- name    : P2M_GroundTheory_Heights__Heights_PlaceCentredSum_deg_ne_zero_16fd8e505679
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:15:09.783968+00:00
-- url     : https://prove2.me/theorems/9683a384-595a-4221-a338-980e027ef693
-- title:
--   P2 M Ground Theory Heights  Heights Place Centred Sum deg ne zero 16fd8e505679: P2 M Ground Theory Heights  Heights Place Centred Sum deg ne zero 16fd8e505679
-- statement:
--   The P2 M Ground Theory Heights  Heights Place Centred Sum deg ne zero 16fd8e505679 construction uses the P2 M Ground Theory Heights  Heights Place Centred Sum deg ne zero 16fd8e505679 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PPlaceCentredSum.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PPlaceCentredSum.lean#L48-L51

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

theorem P2M_GroundTheory_Heights__Heights_PlaceCentredSum_deg_ne_zero_16fd8e505679 (v : FinitePlace K) : deg L v ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PlaceCentredSum».«deg_ne_zero» := P2M_GroundTheory_Heights__Heights_PlaceCentredSum_deg_ne_zero_16fd8e505679
