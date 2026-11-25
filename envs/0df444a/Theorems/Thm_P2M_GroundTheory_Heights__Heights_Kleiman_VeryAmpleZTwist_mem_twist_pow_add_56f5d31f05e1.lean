-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZTwist_mem_twist_pow_add_56f5d31f05e1
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZTwist_mem_twist_pow_add_56f5d31f05e1
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:00:13.39742+00:00
-- url     : https://prove2.me/theorems/ce789811-e703-490f-abd3-b34b676f697e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample ZTwist mem twist pow add 56f5d31f05e1: P2 M Ground Theory Heights  Heights Kleiman Very Ample ZTwist mem twist pow add 56f5d31f05e1
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample ZTwist mem twist pow add 56f5d31f05e1 construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample ZTwist mem twist pow add 56f5d31f05e1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZTwist.lean#L50-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZTwist.lean#L50-L58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZTwistSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZFamilySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleTwistLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZTwist
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
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZTwist
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZTwist_mem_twist_pow_add_56f5d31f05e1 (G : SubSystem S x E) (H : SubSystem S x Ω) (I : Chart x) {a b : ℕ} {z : E}
    (hz : z ∈ ((G.twist (H.pow a)).twist (H.pow b)).sub I) : z ∈ (G.twist (H.pow (a + b))).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleZTwist».«mem_twist_pow_add» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZTwist_mem_twist_pow_add_56f5d31f05e1
