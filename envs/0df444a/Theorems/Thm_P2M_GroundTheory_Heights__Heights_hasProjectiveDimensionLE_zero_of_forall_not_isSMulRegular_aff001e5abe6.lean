-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_hasProjectiveDimensionLE_zero_of_forall_not_isSMulRegular_aff001e5abe6
-- name    : P2M_GroundTheory_Heights__Heights_hasProjectiveDimensionLE_zero_of_forall_not_isSMulRegular_aff001e5abe6
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:46:56.411585+00:00
-- url     : https://prove2.me/theorems/f22d1e57-7950-44fa-9677-7a1930ae5c7f
-- title:
--   P2 M Ground Theory Heights  Heights has Projective Dimension LE zero of forall not is SMul Regular aff001e5abe6: P2 M Ground Theory Heights  Heights has Projective Dimension LE zero of forall not is S
-- statement:
--   The P2 M Ground Theory Heights  Heights has Projective Dimension LE zero of forall not is SMul Regular aff001e5abe6 construction uses the P2 M Ground Theory Heights  Heights has Projective Dimension LE zero of forall not is SMul Regular aff001e5abe6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/AuslanderBuchsbaumDepthBound.lean#L32-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/AuslanderBuchsbaumDepthBound.lean#L32-L39

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

theorem P2M_GroundTheory_Heights__Heights_hasProjectiveDimensionLE_zero_of_forall_not_isSMulRegular_aff001e5abe6 [IsLocalRing R] [IsNoetherianRing R]
    (h : ∀ y ∈ maximalIdeal R, ¬ IsSMulRegular R y) (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] (k : ℕ) (hM : HasProjectiveDimensionLT (ModuleCat.of R M) (k + 1)) :
    HasProjectiveDimensionLE (ModuleCat.of R M) 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«hasProjectiveDimensionLE_zero_of_forall_not_isSMulRegular» := P2M_GroundTheory_Heights__Heights_hasProjectiveDimensionLE_zero_of_forall_not_isSMulRegular_aff001e5abe6
