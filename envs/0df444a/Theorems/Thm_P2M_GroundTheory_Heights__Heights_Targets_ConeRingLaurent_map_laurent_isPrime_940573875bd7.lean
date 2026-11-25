-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ConeRingLaurent_map_laurent_isPrime_940573875bd7
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ConeRingLaurent_map_laurent_isPrime_940573875bd7
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:17:20.713077+00:00
-- url     : https://prove2.me/theorems/f9f64288-2356-46a7-8646-5f422ea94b21
-- title:
--   P2 M Ground Theory Heights  Heights Targets Cone Ring Laurent map laurent is Prime 940573875bd7: P2 M Ground Theory Heights  Heights Targets Cone Ring Laurent map laurent is Prime 940573875bd7
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Cone Ring Laurent map laurent is Prime 940573875bd7 construction uses the P2 M Ground Theory Heights  Heights Targets Cone Ring Laurent map laurent is Prime 940573875bd7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PConeRingLaurent.lean#L115-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PConeRingLaurent.lean#L115-L132

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

theorem P2M_GroundTheory_Heights__Heights_Targets_ConeRingLaurent_map_laurent_isPrime_940573875bd7 (𝔮 : Ideal (DehomRing i)) [𝔮.IsPrime] :
    (𝔮.map (algebraMap (DehomRing i) (Laurent i))).IsPrime := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ConeRingLaurent».«map_laurent_isPrime» := P2M_GroundTheory_Heights__Heights_Targets_ConeRingLaurent_map_laurent_isPrime_940573875bd7
