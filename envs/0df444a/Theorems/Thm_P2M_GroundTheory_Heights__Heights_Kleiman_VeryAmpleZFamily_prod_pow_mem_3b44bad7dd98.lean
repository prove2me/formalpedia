-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFamily_prod_pow_mem_3b44bad7dd98
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFamily_prod_pow_mem_3b44bad7dd98
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:03:41.177218+00:00
-- url     : https://prove2.me/theorems/339a448b-b837-432b-8e92-9d53df7505d1
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample ZFamily prod pow mem 3b44bad7dd98: P2 M Ground Theory Heights  Heights Kleiman Very Ample ZFamily prod pow mem 3b44bad7dd98
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample ZFamily prod pow mem 3b44bad7dd98 construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample ZFamily prod pow mem 3b44bad7dd98 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZFamily.lean#L65-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZFamily.lean#L65-L69

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFamily_prod_pow_mem_3b44bad7dd98 (H : SubSystem S x Ω) (I : Chart x) (hh : ∀ l, h l ∈ H.sub I)
    (T : Finset (Fin (r + 1))) (n : ℕ) : (∏ l ∈ T, h l) ^ n ∈ (H.pow (T.card * n)).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleZFamily».«prod_pow_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFamily_prod_pow_mem_3b44bad7dd98
