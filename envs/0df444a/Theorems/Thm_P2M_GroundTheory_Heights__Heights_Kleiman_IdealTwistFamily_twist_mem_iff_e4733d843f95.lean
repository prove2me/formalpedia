-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_twist_mem_iff_e4733d843f95
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_twist_mem_iff_e4733d843f95
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T06:15:53.562361+00:00
-- url     : https://prove2.me/theorems/6faa3f71-fb46-5eb4-b966-28717f01835e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ideal Twist Family twist mem iff e4733d843f95: P2 M Ground Theory Heights  Heights Kleiman Ideal Twist Family twist mem iff e4733d843f95
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ideal Twist Family twist mem iff e4733d843f95 construction uses the P2 M Ground Theory Heights  Heights Kleiman Ideal Twist Family twist mem iff e4733d843f95 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PIdealTwistFamily.lean#L196-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PIdealTwistFamily.lean#L196-L221

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_twist_mem_iff_e4733d843f95 (Q : LineBundle S x) (J' : Ideal (Poly S N)) (I J : Chart x)
    (h : I.1 ⊆ J.1) (y : Ω) :
    y ∈ (Q.twist (idealSys x J')).sub J ↔ ∃ a : chartRing S x I, IsUnit (chartIncl h a) ∧
      (a : Ω) • y ∈ (Q.twist (idealSys x J')).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«IdealTwistFamily».«twist_mem_iff» := P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_twist_mem_iff_e4733d843f95
