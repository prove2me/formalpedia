-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_pow_mono_40872ba2f21e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_pow_mono_40872ba2f21e
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:13:19.189894+00:00
-- url     : https://prove2.me/theorems/dd61d109-1cd7-5262-9cd7-8f6e422f5304
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample ZColumns pow mono 40872ba2f21e: P2 M Ground Theory Heights  Heights Kleiman Very Ample ZColumns pow mono 40872ba2f21e
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample ZColumns pow mono 40872ba2f21e construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample ZColumns pow mono 40872ba2f21e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZColumns.lean#L84-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZColumns.lean#L84-L91

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZColumnsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZColumnsCechPartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZColumns
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
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZColumns
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  {r : ℕ}
variable {G : SubSystem S x E} {H : SubSystem S x Ω} {h : Fin (r + 1) → Ω} {I : Chart x}
omit [Module S E] [IsScalarTower S Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_pow_mono_40872ba2f21e (hH : ∀ j, h j ∈ H.sub I) {J : Chart h} {e : E} {n : ℕ}
    (he : xProd J ^ n • e ∈ (G.twist (H.pow (J.1.card * n))).sub I) (k : ℕ) :
    xProd J ^ (n + k) • e ∈ (G.twist (H.pow (J.1.card * (n + k)))).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleZColumns».«pow_mono» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_pow_mono_40872ba2f21e
