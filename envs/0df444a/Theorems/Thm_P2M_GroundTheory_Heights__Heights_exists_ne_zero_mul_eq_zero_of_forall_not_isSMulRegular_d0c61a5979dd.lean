-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_ne_zero_mul_eq_zero_of_forall_not_isSMulRegular_d0c61a5979dd
-- name    : P2M_GroundTheory_Heights__Heights_exists_ne_zero_mul_eq_zero_of_forall_not_isSMulRegular_d0c61a5979dd
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:46:28.792909+00:00
-- url     : https://prove2.me/theorems/94f491d3-2a4b-4bd1-80fc-1fd3b3b765af
-- title:
--   P2 M Ground Theory Heights  Heights exists ne zero mul eq zero of forall not is SMul Regular d0c61a5979dd: P2 M Ground Theory Heights  Heights exists ne zero mul eq zero of forall not is SMul Regular
-- statement:
--   The P2 M Ground Theory Heights  Heights exists ne zero mul eq zero of forall not is SMul Regular d0c61a5979dd construction uses the P2 M Ground Theory Heights  Heights exists ne zero mul eq zero of forall not is SMul Regular d0c61a5979dd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/AuslanderBuchsbaumDepthBound.lean#L14-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/AuslanderBuchsbaumDepthBound.lean#L14-L30

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

theorem P2M_GroundTheory_Heights__Heights_exists_ne_zero_mul_eq_zero_of_forall_not_isSMulRegular_d0c61a5979dd [IsLocalRing R] [IsNoetherianRing R]
    (h : ∀ y ∈ maximalIdeal R, ¬ IsSMulRegular R y) :
    ∃ s : R, s ≠ 0 ∧ ∀ a ∈ maximalIdeal R, a * s = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_ne_zero_mul_eq_zero_of_forall_not_isSMulRegular» := P2M_GroundTheory_Heights__Heights_exists_ne_zero_mul_eq_zero_of_forall_not_isSMulRegular_d0c61a5979dd
