-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFamily_exists_mul_xProd_pow_mem_fd9a69082dcf
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFamily_exists_mul_xProd_pow_mem_fd9a69082dcf
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:05:49.274939+00:00
-- url     : https://prove2.me/theorems/81c799ac-62f1-53fe-b37a-24373b6cdc93
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample ZFamily exists mul x Prod pow mem fd9a69082dcf: P2 M Ground Theory Heights  Heights Kleiman Very Ample ZFamily exists mul x Prod pow mem fd9a6908
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample ZFamily exists mul x Prod pow mem fd9a69082dcf construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample ZFamily exists mul x Prod pow mem fd9a69082dcf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZFamily.lean#L115-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZFamily.lean#L115-L137

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFamily_exists_mul_xProd_pow_mem_fd9a69082dcf (H : SubSystem S x Ω) (I : Chart x) (hh : ∀ l, h l ∈ H.sub I)
    (J : Chart h) {a : Ω} (ha : a ∈ chartRing S h J) :
    ∃ k : ℕ, a * xProd J ^ k ∈ (H.pow (J.1.card * k)).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleZFamily».«exists_mul_xProd_pow_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFamily_exists_mul_xProd_pow_mem_fd9a69082dcf
