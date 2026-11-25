-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZTwist_smul_mem_twist_pow_7d26be4ef798
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZTwist_smul_mem_twist_pow_7d26be4ef798
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:57:59.552484+00:00
-- url     : https://prove2.me/theorems/36e4153b-6f51-4cc6-9d75-015df0d7e54d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample ZTwist smul mem twist pow 7d26be4ef798: P2 M Ground Theory Heights  Heights Kleiman Very Ample ZTwist smul mem twist pow 7d26be4ef798
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample ZTwist smul mem twist pow 7d26be4ef798 construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample ZTwist smul mem twist pow 7d26be4ef798 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZTwist.lean#L36-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZTwist.lean#L36-L48

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZTwist_smul_mem_twist_pow_7d26be4ef798 (G : SubSystem S x E) (H : SubSystem S x Ω) (I : Chart x) {c d : ℕ} {w : Ω}
    (hw : w ∈ (H.pow c).sub I) {z : E} (hz : z ∈ (G.twist (H.pow d)).sub I) :
    w • z ∈ (G.twist (H.pow (d + c))).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleZTwist».«smul_mem_twist_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZTwist_smul_mem_twist_pow_7d26be4ef798
