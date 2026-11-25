-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_homogeneousComponent_mul_form_2336838196fb
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_homogeneousComponent_mul_form_2336838196fb
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:14:47.143981+00:00
-- url     : https://prove2.me/theorems/392b672c-5d93-4b33-a200-63f639f2aaff
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ideal Twist Family homogeneous Component mul form 2336838196fb: P2 M Ground Theory Heights  Heights Kleiman Ideal Twist Family homogeneous Component mul for
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ideal Twist Family homogeneous Component mul form 2336838196fb construction uses the P2 M Ground Theory Heights  Heights Kleiman Ideal Twist Family homogeneous Component mul form 2336838196fb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PIdealTwistFamily.lean#L19-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PIdealTwistFamily.lean#L19-L30

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_homogeneousComponent_mul_form_2336838196fb (r g : Poly R N) {d : ℕ} (hg : g.IsHomogeneous d) (e : ℕ) :
    homogeneousComponent e (r * g) ∈ Submodule.span R
      {z | ∃ (h : Poly R N) (d' : ℕ), h.IsHomogeneous d' ∧ d' + d = e ∧ z = h * g} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«IdealTwistFamily».«homogeneousComponent_mul_form» := P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_homogeneousComponent_mul_form_2336838196fb
