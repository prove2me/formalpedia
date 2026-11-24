-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_isHomogeneous_span_of_6218751a8226
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_isHomogeneous_span_of_6218751a8226
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:44:13.603801+00:00
-- url     : https://prove2.me/theorems/fd56aaa4-5bf9-42ab-8e67-a005a8a0c9e9
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Sec BFinite is Homogeneous span of 6218751a8226: P2 M Ground Theory Heights  Heights Vertical Sec BFinite is Homogeneous span of 6218751a8226
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Sec BFinite is Homogeneous span of 6218751a8226 construction uses the P2 M Ground Theory Heights  Heights Vertical Sec BFinite is Homogeneous span of 6218751a8226 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBFinite.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBFinite.lean#L39-L43

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_isHomogeneous_span_of_6218751a8226 {s : Set (MvPolynomial σ R)} (h : ∀ x ∈ s, ∃ d, x.IsHomogeneous d) :
    (Ideal.span s).IsHomogeneous (homogeneousSubmodule σ R) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SecBFinite».«isHomogeneous_span_of» := P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_isHomogeneous_span_of_6218751a8226
