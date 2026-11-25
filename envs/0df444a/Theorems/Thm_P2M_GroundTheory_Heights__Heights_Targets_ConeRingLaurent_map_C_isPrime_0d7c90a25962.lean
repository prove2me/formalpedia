-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ConeRingLaurent_map_C_isPrime_0d7c90a25962
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ConeRingLaurent_map_C_isPrime_0d7c90a25962
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:16:41.97932+00:00
-- url     : https://prove2.me/theorems/435b6c46-3053-45be-89c1-fe73dfbb61c8
-- title:
--   P2 M Ground Theory Heights  Heights Targets Cone Ring Laurent map C is Prime 0d7c90a25962: P2 M Ground Theory Heights  Heights Targets Cone Ring Laurent map C is Prime 0d7c90a25962
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Cone Ring Laurent map C is Prime 0d7c90a25962 construction uses the P2 M Ground Theory Heights  Heights Targets Cone Ring Laurent map C is Prime 0d7c90a25962 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PConeRingLaurent.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PConeRingLaurent.lean#L13-L16

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

theorem P2M_GroundTheory_Heights__Heights_Targets_ConeRingLaurent_map_C_isPrime_0d7c90a25962 {D σ : Type*} [CommRing D] (𝔮 : Ideal D) [𝔮.IsPrime] :
    (𝔮.map (C : D →+* MvPolynomial σ D)).IsPrime := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ConeRingLaurent».«map_C_isPrime» := P2M_GroundTheory_Heights__Heights_Targets_ConeRingLaurent_map_C_isPrime_0d7c90a25962
