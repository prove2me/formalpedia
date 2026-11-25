-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_homogeneousComponent_mul_of_deg_one_f4bb220a562a
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_homogeneousComponent_mul_of_deg_one_f4bb220a562a
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:43:49.068024+00:00
-- url     : https://prove2.me/theorems/f09735d2-c3b8-52d5-b3d4-22ea6d344ad3
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Sec BFinite homogeneous Component mul of deg one f4bb220a562a: P2 M Ground Theory Heights  Heights Vertical Sec BFinite homogeneous Component mul of deg on
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Sec BFinite homogeneous Component mul of deg one f4bb220a562a construction uses the P2 M Ground Theory Heights  Heights Vertical Sec BFinite homogeneous Component mul of deg one f4bb220a562a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBFinite.lean#L28-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBFinite.lean#L28-L37

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_homogeneousComponent_mul_of_deg_one_f4bb220a562a (c t : MvPolynomial σ R) (ht : t.IsHomogeneous 1) (d : ℕ) :
    homogeneousComponent (d + 1) (c * t) = homogeneousComponent d c * t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SecBFinite».«homogeneousComponent_mul_of_deg_one» := P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_homogeneousComponent_mul_of_deg_one_f4bb220a562a
