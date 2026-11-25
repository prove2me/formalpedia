-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZExtend_smul_mem_twist_pow_e1c974636e30
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZExtend_smul_mem_twist_pow_e1c974636e30
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:08:58.427117+00:00
-- url     : https://prove2.me/theorems/bd52d0f4-7bce-4ba5-8192-565e8ea2defa
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample ZExtend smul mem twist pow e1c974636e30: P2 M Ground Theory Heights  Heights Kleiman Very Ample ZExtend smul mem twist pow e1c974636e30
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample ZExtend smul mem twist pow e1c974636e30 construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample ZExtend smul mem twist pow e1c974636e30 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZExtend.lean#L33-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZExtend.lean#L33-L47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsVeryAmpleZFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZExtend
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
open Filter
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZExtend
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
omit [Module S E] [IsScalarTower S Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZExtend_smul_mem_twist_pow_e1c974636e30 (F : SubSystem S x E) (H : SubSystem S x Ω) (I : Chart x) {a b : ℕ} {z : E}
    {w : Ω} (hz : z ∈ (F.twist (H.pow a)).sub I) (hw : w ∈ (H.pow b).sub I) :
    w • z ∈ (F.twist (H.pow (a + b))).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleZExtend».«smul_mem_twist_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZExtend_smul_mem_twist_pow_e1c974636e30
