-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZExtend_gen_smul_e549be2950d7
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZExtend_gen_smul_e549be2950d7
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:02:43.008897+00:00
-- url     : https://prove2.me/theorems/3c3fe2e6-bd63-4637-b7ba-49c888753761
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample ZExtend gen smul e549be2950d7: P2 M Ground Theory Heights  Heights Kleiman Very Ample ZExtend gen smul e549be2950d7
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample ZExtend gen smul e549be2950d7 construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample ZExtend gen smul e549be2950d7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZExtend.lean#L51-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZExtend.lean#L51-L71

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZExtend_gen_smul_e549be2950d7 {r : ℕ} (F : SubSystem S x E) (H : SubSystem S x Ω) {h : Fin (r + 1) → Ω}
    (hh : ∀ l, h l ∈ H.secs) (I : Chart x) (J : Chart h) {j : Fin (r + 1)} (hj : j ∈ J.1) {c : Ω} {a : ℕ}
    (hc : c * h j ^ a ∈ (H.pow a).sub I) {y : E}
    (hy : ∃ m : ℕ, xProd J ^ m • y ∈ (F.twist (H.pow (J.1.card * m))).sub I) :
    ∃ m : ℕ, xProd J ^ m • (c • y) ∈ (F.twist (H.pow (J.1.card * m))).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleZExtend».«gen_smul» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZExtend_gen_smul_e549be2950d7
