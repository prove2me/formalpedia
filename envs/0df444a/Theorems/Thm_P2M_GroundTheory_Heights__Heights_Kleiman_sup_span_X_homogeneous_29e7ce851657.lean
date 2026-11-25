-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_sup_span_X_homogeneous_29e7ce851657
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_sup_span_X_homogeneous_29e7ce851657
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:02:58.734742+00:00
-- url     : https://prove2.me/theorems/5b1392ec-40fc-49f3-9184-9a4a254bcafc
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman sup span X homogeneous 29e7ce851657: P2 M Ground Theory Heights  Heights Kleiman sup span X homogeneous 29e7ce851657
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman sup span X homogeneous 29e7ce851657 construction uses the P2 M Ground Theory Heights  Heights Kleiman sup span X homogeneous 29e7ce851657 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperHyperplane.lean#L67-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperHyperplane.lean#L67-L79

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PIdealTwistFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneMidSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotAddSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperHyperplane
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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_sup_span_X_homogeneous_29e7ce851657 {R : Type u} [CommRing R] {N : ℕ} (pp : Ideal (Poly R N))
    (hh : ∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) (i : Fin (N + 1)) :
    ∀ f ∈ pp ⊔ Ideal.span {(X i : Poly R N)}, ∀ d : ℕ,
      homogeneousComponent d f ∈ pp ⊔ Ideal.span {(X i : Poly R N)} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«sup_span_X_homogeneous» := P2M_GroundTheory_Heights__Heights_Kleiman_sup_span_X_homogeneous_29e7ce851657
