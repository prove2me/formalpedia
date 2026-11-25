-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootsLiftToZeros_exists_extend_c6312c5192ff
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootsLiftToZeros_exists_extend_c6312c5192ff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:26.329515+00:00
-- url     : https://prove2.me/theorems/d333fb87-3ff8-4a8d-adcd-210b3b21289c
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Roots Lift To Zeros exists extend c6312c5192ff: P2 M Ground Theory Heights  Heights Hilbert Samuel Roots Lift To Zeros exists extend c6312c5192ff
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Roots Lift To Zeros exists extend c6312c5192ff construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Roots Lift To Zeros exists extend c6312c5192ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PRootsLiftToZeros.lean#L10-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PRootsLiftToZeros.lean#L10-L13

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRootsLiftToZeros
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsMoreRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PRootsLiftToZeros
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootsLiftToZeros_exists_extend_c6312c5192ff {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.IsIntegral R A] (ev : R →+* ℂ) (hker : RingHom.ker (algebraMap R A) ≤ RingHom.ker ev) :
    ∃ χ : A →+* ℂ, χ.comp (algebraMap R A) = ev := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«RootsLiftToZeros».«exists_extend» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootsLiftToZeros_exists_extend_c6312c5192ff
