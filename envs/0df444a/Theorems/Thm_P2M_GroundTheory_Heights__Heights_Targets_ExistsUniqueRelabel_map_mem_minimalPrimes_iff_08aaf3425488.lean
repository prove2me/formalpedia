-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_map_mem_minimalPrimes_iff_08aaf3425488
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_map_mem_minimalPrimes_iff_08aaf3425488
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:27:11.104627+00:00
-- url     : https://prove2.me/theorems/d6cbd588-8d8b-52a8-95c5-96505efac248
-- title:
--   P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel map mem minimal Primes iff 08aaf3425488: P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel map mem minimal Primes iff
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel map mem minimal Primes iff 08aaf3425488 construction uses the P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel map mem minimal Primes iff 08aaf3425488 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PExistsUniqueRelabel.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PExistsUniqueRelabel.lean#L26-L30

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ExistsUnique
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.Targets.ExistsUniqueRelabel
variable {R R' : Type*} [CommRing R] [CommRing R'] (φ : R ≃+* R')

theorem P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_map_mem_minimalPrimes_iff_08aaf3425488 {J W : Ideal R} :
    W.map (φ : R →+* R') ∈ (J.map (φ : R →+* R')).minimalPrimes ↔ W ∈ J.minimalPrimes := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ExistsUniqueRelabel».«map_mem_minimalPrimes_iff» := P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_map_mem_minimalPrimes_iff_08aaf3425488
