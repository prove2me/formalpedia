-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_map_of_mul_mem_map_84f21a973d11
-- name    : P2M_GroundTheory_Heights__Heights_mem_map_of_mul_mem_map_84f21a973d11
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:49:17.09899+00:00
-- url     : https://prove2.me/theorems/52fe8333-12fb-484c-97b2-005691bd7be8
-- title:
--   P2 M Ground Theory Heights  Heights mem map of mul mem map 84f21a973d11: P2 M Ground Theory Heights  Heights mem map of mul mem map 84f21a973d11
-- statement:
--   The P2 M Ground Theory Heights  Heights mem map of mul mem map 84f21a973d11 construction uses the P2 M Ground Theory Heights  Heights mem map of mul mem map 84f21a973d11 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFibreRadicalPrime.lean#L170-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericFibreRadicalPrime.lean#L170-L192

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreRadicalPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreTor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHypersurfacePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFibreRadicalPrime
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
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_mem_map_of_mul_mem_map_84f21a973d11 {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R')
    (hφ : Function.Surjective φ) (K : Ideal R) (hK : K.IsPrime) (b : R) (hb : b ∉ K)
    (h : (K ⊔ Ideal.span {b}) ⊓ RingHom.ker φ ≤ RingHom.ker φ * (K ⊔ Ideal.span {b}))
    (g : R') (hg : φ b * g ∈ K.map φ) : g ∈ K.map φ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mem_map_of_mul_mem_map» := P2M_GroundTheory_Heights__Heights_mem_map_of_mul_mem_map_84f21a973d11
