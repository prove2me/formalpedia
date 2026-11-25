-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZTwist_smul_mem_twist_twist_83284b5696ee
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZTwist_smul_mem_twist_twist_83284b5696ee
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:12:24.128708+00:00
-- url     : https://prove2.me/theorems/271213d0-9670-451d-9dc9-a71052430239
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample ZTwist smul mem twist twist 83284b5696ee: P2 M Ground Theory Heights  Heights Kleiman Very Ample ZTwist smul mem twist twist 83284b5696ee
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample ZTwist smul mem twist twist 83284b5696ee construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample ZTwist smul mem twist twist 83284b5696ee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZTwist.lean#L23-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZTwist.lean#L23-L34

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZTwist_smul_mem_twist_twist_83284b5696ee (G : SubSystem S x E) (P Q : SubSystem S x Ω) (I : Chart x) {q : Ω}
    (hq : q ∈ P.sub I) {z : E} (hz : z ∈ (G.twist Q).sub I) : q • z ∈ ((G.twist P).twist Q).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleZTwist».«smul_mem_twist_twist» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZTwist_smul_mem_twist_twist_83284b5696ee
