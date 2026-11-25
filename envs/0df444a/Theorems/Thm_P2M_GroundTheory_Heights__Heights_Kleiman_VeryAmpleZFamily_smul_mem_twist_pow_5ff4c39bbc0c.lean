-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFamily_smul_mem_twist_pow_5ff4c39bbc0c
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFamily_smul_mem_twist_pow_5ff4c39bbc0c
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:02:42.237046+00:00
-- url     : https://prove2.me/theorems/3420ecd7-ffa7-5c60-ab53-b4723a5fedd8
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample ZFamily smul mem twist pow 5ff4c39bbc0c: P2 M Ground Theory Heights  Heights Kleiman Very Ample ZFamily smul mem twist pow 5ff4c39bbc0c
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample ZFamily smul mem twist pow 5ff4c39bbc0c construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample ZFamily smul mem twist pow 5ff4c39bbc0c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZFamily.lean#L47-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZFamily.lean#L47-L60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZFamilySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZFamily
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
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZFamily
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  {r : ℕ} {h : Fin (r + 1) → Ω}
omit [Module S E] [IsScalarTower S Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFamily_smul_mem_twist_pow_5ff4c39bbc0c (F : SubSystem S x E) (H : SubSystem S x Ω) (I : Chart x) {c d : ℕ} {z : E}
    {q : Ω} (hz : z ∈ (F.twist (H.pow c)).sub I) (hq : q ∈ (H.pow d).sub I) :
    q • z ∈ (F.twist (H.pow (c + d))).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleZFamily».«smul_mem_twist_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFamily_smul_mem_twist_pow_5ff4c39bbc0c
