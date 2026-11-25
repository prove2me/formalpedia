-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_map_mem_minimalPrimes_063d0b2c83a5
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_map_mem_minimalPrimes_063d0b2c83a5
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:41:14.169829+00:00
-- url     : https://prove2.me/theorems/87e909c0-a0d7-5677-aa43-b506fed12f24
-- title:
--   P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel map mem minimal Primes 063d0b2c83a5: P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel map mem minimal Primes 063d0b2c
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel map mem minimal Primes 063d0b2c83a5 construction uses the P2 M Ground Theory Heights  Heights Targets Exists Unique Relabel map mem minimal Primes 063d0b2c83a5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PExistsUniqueRelabel.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PExistsUniqueRelabel.lean#L21-L24

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

theorem P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_map_mem_minimalPrimes_063d0b2c83a5 {J W : Ideal R} (h : W ∈ J.minimalPrimes) :
    W.map (φ : R →+* R') ∈ (J.map (φ : R →+* R')).minimalPrimes := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ExistsUniqueRelabel».«map_mem_minimalPrimes» := P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_map_mem_minimalPrimes_063d0b2c83a5
