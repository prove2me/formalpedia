-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_exists_finset_forms_7e62cb2b7e9a
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_exists_finset_forms_7e62cb2b7e9a
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:55:35.185125+00:00
-- url     : https://prove2.me/theorems/3bd13e42-cd1a-4a1d-a0f3-78fe22de7d99
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ideal Twist Family exists finset forms 7e62cb2b7e9a: P2 M Ground Theory Heights  Heights Kleiman Ideal Twist Family exists finset forms 7e62cb2b7e9a
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ideal Twist Family exists finset forms 7e62cb2b7e9a construction uses the P2 M Ground Theory Heights  Heights Kleiman Ideal Twist Family exists finset forms 7e62cb2b7e9a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PIdealTwistFamily.lean#L52-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PIdealTwistFamily.lean#L52-L78

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_exists_finset_forms_7e62cb2b7e9a [IsNoetherianRing R] (J : Ideal (Poly R N))
    (hJ : ∀ p ∈ J, ∀ d : ℕ, homogeneousComponent d p ∈ J) :
    ∃ H : Finset (Poly R N), (↑H : Set (Poly R N)) ⊆ J ∧ Ideal.span (↑H : Set (Poly R N)) = J ∧
      ∀ g ∈ (↑H : Set (Poly R N)), g.IsHomogeneous g.totalDegree := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«IdealTwistFamily».«exists_finset_forms» := P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_exists_finset_forms_7e62cb2b7e9a
