-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_hasProjectiveDimensionLT_of_quotSMulTop_588b6ec3e228
-- name    : P2M_GroundTheory_Heights__Heights_hasProjectiveDimensionLT_of_quotSMulTop_588b6ec3e228
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:46:57.35017+00:00
-- url     : https://prove2.me/theorems/8a9baf3d-60e3-4e7e-a104-59356cc88f3c
-- title:
--   P2 M Ground Theory Heights  Heights has Projective Dimension LT of quot SMul Top 588b6ec3e228: P2 M Ground Theory Heights  Heights has Projective Dimension LT of quot SMul Top 588b6ec3e228
-- statement:
--   The P2 M Ground Theory Heights  Heights has Projective Dimension LT of quot SMul Top 588b6ec3e228 construction uses the P2 M Ground Theory Heights  Heights has Projective Dimension LT of quot SMul Top 588b6ec3e228 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/AuslanderBuchsbaumDepthBound.lean#L41-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/AuslanderBuchsbaumDepthBound.lean#L41-L103

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDLocalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AuslanderBuchsbaumDepthBound
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
open IsLocalRing CategoryTheory RingTheory.Sequence Ideal
open scoped Pointwise
universe u
variable {R : Type u} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_hasProjectiveDimensionLT_of_quotSMulTop_588b6ec3e228 [IsLocalRing R] [IsNoetherianRing R] {x : R}
    (hx : x ∈ maximalIdeal R) (hxR : IsSMulRegular R x) (k : ℕ) (M : Type u) [AddCommGroup M]
    [Module R M] [Module.Finite R M] (hxM : IsSMulRegular M x)
    (hM : HasProjectiveDimensionLT (ModuleCat.of (R ⧸ span {x}) (QuotSMulTop x M)) (k + 1)) :
    HasProjectiveDimensionLT (ModuleCat.of R M) (k + 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«hasProjectiveDimensionLT_of_quotSMulTop» := P2M_GroundTheory_Heights__Heights_hasProjectiveDimensionLT_of_quotSMulTop_588b6ec3e228
