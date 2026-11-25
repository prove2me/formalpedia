-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_isHomogeneous_map_of_c719dbf86e3f
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_isHomogeneous_map_of_c719dbf86e3f
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:43:17.066909+00:00
-- url     : https://prove2.me/theorems/a22793b0-0549-4f4c-bf94-d03e9d2ddee9
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Sec BFinite is Homogeneous map of c719dbf86e3f: P2 M Ground Theory Heights  Heights Vertical Sec BFinite is Homogeneous map of c719dbf86e3f
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Sec BFinite is Homogeneous map of c719dbf86e3f construction uses the P2 M Ground Theory Heights  Heights Vertical Sec BFinite is Homogeneous map of c719dbf86e3f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBFinite.lean#L45-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBFinite.lean#L45-L61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.SecBFinite
variable {σ R S : Type*} [CommRing R] [CommRing S]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_isHomogeneous_map_of_c719dbf86e3f (f : R →+* S) (P : Ideal (MvPolynomial σ R))
    (hP : ∀ p ∈ P, ∀ d, homogeneousComponent d p ∈ P) :
    (P.map (MvPolynomial.map f)).IsHomogeneous (homogeneousSubmodule σ S) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SecBFinite».«isHomogeneous_map_of» := P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_isHomogeneous_map_of_c719dbf86e3f
