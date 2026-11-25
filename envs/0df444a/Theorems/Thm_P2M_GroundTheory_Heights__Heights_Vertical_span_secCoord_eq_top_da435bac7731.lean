-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_span_secCoord_eq_top_da435bac7731
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_span_secCoord_eq_top_da435bac7731
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:44:34.569853+00:00
-- url     : https://prove2.me/theorems/9eee7306-df57-4449-ad46-00283c1ceb4e
-- title:
--   P2 M Ground Theory Heights  Heights Vertical span sec Coord eq top da435bac7731: P2 M Ground Theory Heights  Heights Vertical span sec Coord eq top da435bac7731
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical span sec Coord eq top da435bac7731 construction uses the P2 M Ground Theory Heights  Heights Vertical span sec Coord eq top da435bac7731 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBTorsionFree.lean#L15-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBTorsionFree.lean#L15-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBTorsionFree
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
variable {R : Type*} [CommRing R] {n e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Vertical_span_secCoord_eq_top_da435bac7731 (Q : Ideal (MvPolynomial (Fin n) R)) (y : Par e n → R) :
    Ideal.span (Set.range (secCoord Q y)) = ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«span_secCoord_eq_top» := P2M_GroundTheory_Heights__Heights_Vertical_span_secCoord_eq_top_da435bac7731
