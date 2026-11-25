-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ConeRingLaurent_toCone_comp_algebraMap_5f26f5acad7d
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ConeRingLaurent_toCone_comp_algebraMap_5f26f5acad7d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:17:35.005742+00:00
-- url     : https://prove2.me/theorems/6a10a50f-a3ba-49ff-850f-5d2145c2ac28
-- title:
--   P2 M Ground Theory Heights  Heights Targets Cone Ring Laurent to Cone comp algebra Map 5f26f5acad7d: P2 M Ground Theory Heights  Heights Targets Cone Ring Laurent to Cone comp algebra Map 5f26f5acad7d
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Cone Ring Laurent to Cone comp algebra Map 5f26f5acad7d construction uses the P2 M Ground Theory Heights  Heights Targets Cone Ring Laurent to Cone comp algebra Map 5f26f5acad7d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PConeRingLaurent.lean#L110-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PConeRingLaurent.lean#L110-L113

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StConeRingLaurent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PConeRingLaurent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
open GroundTheory.Heights₂.Heights.Targets.ConeRingLaurent
variable {K : Type} [Fintype K] {ι : K → Type} (i : (k : K) → ι k)

theorem P2M_GroundTheory_Heights__Heights_Targets_ConeRingLaurent_toCone_comp_algebraMap_5f26f5acad7d : (toCone i).comp (algebraMap (DehomRing i) (Laurent i)) = ratioMap i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ConeRingLaurent».«toCone_comp_algebraMap» := P2M_GroundTheory_Heights__Heights_Targets_ConeRingLaurent_toCone_comp_algebraMap_5f26f5acad7d
