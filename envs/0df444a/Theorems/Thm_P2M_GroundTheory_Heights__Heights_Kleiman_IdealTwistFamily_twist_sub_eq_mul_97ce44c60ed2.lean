-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_twist_sub_eq_mul_97ce44c60ed2
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_twist_sub_eq_mul_97ce44c60ed2
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:55:09.895837+00:00
-- url     : https://prove2.me/theorems/1f0e94ff-169a-4aae-8f3d-739a899ede2d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ideal Twist Family twist sub eq mul 97ce44c60ed2: P2 M Ground Theory Heights  Heights Kleiman Ideal Twist Family twist sub eq mul 97ce44c60ed2
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ideal Twist Family twist sub eq mul 97ce44c60ed2 construction uses the P2 M Ground Theory Heights  Heights Kleiman Ideal Twist Family twist sub eq mul 97ce44c60ed2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PIdealTwistFamily.lean#L87-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PIdealTwistFamily.lean#L87-L98

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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_twist_sub_eq_mul_97ce44c60ed2 (F Q : SubSystem S x Ω) (I : Chart x) :
    (F.twist Q).sub I = Q.sub I * F.sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«IdealTwistFamily».«twist_sub_eq_mul» := P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_twist_sub_eq_mul_97ce44c60ed2
