-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_homogeneousComponent_homog_mul_e19dd5398082
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_homogeneousComponent_homog_mul_e19dd5398082
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:11:02.161844+00:00
-- url     : https://prove2.me/theorems/2f4ad9c3-fb1e-4b8e-8333-8910a402f6dc
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Step Three Away homogeneous Component homog mul e19dd5398082: P2 M Ground Theory Heights  Heights Kleiman Step Three Away homogeneous Component homog mul e1
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Step Three Away homogeneous Component homog mul e19dd5398082 construction uses the P2 M Ground Theory Heights  Heights Kleiman Step Three Away homogeneous Component homog mul e19dd5398082 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeAway.lean#L20-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeAway.lean#L20-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeAway
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
open GroundTheory.Heights₂.Heights.Kleiman.StepThree GroundTheory.Heights₂.Heights.Kleiman.StepThree.Away
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_homogeneousComponent_homog_mul_e19dd5398082 {σ R : Type*} [CommRing R] {P : MvPolynomial σ R} {l : ℕ}
    (hP : P.IsHomogeneous l) (G : MvPolynomial σ R) (d : ℕ) :
    homogeneousComponent d (P * G) =
      if l ≤ d then P * homogeneousComponent (d - l) G else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«StepThree».«Away».«homogeneousComponent_homog_mul» := P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_homogeneousComponent_homog_mul_e19dd5398082
