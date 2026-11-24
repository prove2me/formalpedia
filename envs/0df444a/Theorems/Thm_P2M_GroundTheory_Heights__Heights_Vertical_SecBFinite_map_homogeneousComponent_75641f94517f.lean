-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_map_homogeneousComponent_75641f94517f
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_map_homogeneousComponent_75641f94517f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:39.10932+00:00
-- url     : https://prove2.me/theorems/66218d0e-5709-45c4-bcb6-37113a32276e
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Sec BFinite map homogeneous Component 75641f94517f: P2 M Ground Theory Heights  Heights Vertical Sec BFinite map homogeneous Component 75641f94517f
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Sec BFinite map homogeneous Component 75641f94517f construction uses the P2 M Ground Theory Heights  Heights Vertical Sec BFinite map homogeneous Component 75641f94517f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBFinite.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBFinite.lean#L17-L21

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_map_homogeneousComponent_75641f94517f (f : R →+* S) (d : ℕ) (p : MvPolynomial σ R) :
    MvPolynomial.map f (homogeneousComponent d p) = homogeneousComponent d (MvPolynomial.map f p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SecBFinite».«map_homogeneousComponent» := P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_map_homogeneousComponent_75641f94517f
