-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_mem_span_forms_of_mem_ideal_85d986a9ff48
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_mem_span_forms_of_mem_ideal_85d986a9ff48
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:55:17.2776+00:00
-- url     : https://prove2.me/theorems/df510e67-9a3f-4aea-8cb5-fe8560845ba7
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ideal Twist Family mem span forms of mem ideal 85d986a9ff48: P2 M Ground Theory Heights  Heights Kleiman Ideal Twist Family mem span forms of mem ideal 85d9
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ideal Twist Family mem span forms of mem ideal 85d986a9ff48 construction uses the P2 M Ground Theory Heights  Heights Kleiman Ideal Twist Family mem span forms of mem ideal 85d986a9ff48 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PIdealTwistFamily.lean#L32-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PIdealTwistFamily.lean#L32-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsIdealTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PIdealTwistFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.IdealTwistFamily
variable {R : Type u} [CommRing R] {N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_mem_span_forms_of_mem_ideal_85d986a9ff48 {G : Set (Poly R N)} (deg : Poly R N → ℕ)
    (hG : ∀ g ∈ G, g.IsHomogeneous (deg g)) {f : Poly R N} {e : ℕ} (hf : f ∈ Ideal.span G)
    (he : f.IsHomogeneous e) :
    f ∈ Submodule.span R {z | ∃ g ∈ G, ∃ (h : Poly R N) (d' : ℕ), h.IsHomogeneous d' ∧
      d' + deg g = e ∧ z = h * g} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«IdealTwistFamily».«mem_span_forms_of_mem_ideal» := P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_mem_span_forms_of_mem_ideal_85d986a9ff48
