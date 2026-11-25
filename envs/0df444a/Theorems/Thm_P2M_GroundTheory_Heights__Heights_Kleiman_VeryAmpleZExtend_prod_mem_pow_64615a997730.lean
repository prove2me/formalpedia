-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZExtend_prod_mem_pow_64615a997730
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZExtend_prod_mem_pow_64615a997730
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:08:26.555859+00:00
-- url     : https://prove2.me/theorems/96dfcb33-f59f-493a-862d-82ae5f26c44d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample ZExtend prod mem pow 64615a997730: P2 M Ground Theory Heights  Heights Kleiman Very Ample ZExtend prod mem pow 64615a997730
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample ZExtend prod mem pow 64615a997730 construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample ZExtend prod mem pow 64615a997730 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZExtend.lean#L19-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZExtend.lean#L19-L29

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZExtend_prod_mem_pow_64615a997730 {r : ℕ} (H : SubSystem S x Ω) {h : Fin (r + 1) → Ω} (hh : ∀ l, h l ∈ H.secs)
    (I : Chart x) (T : Finset (Fin (r + 1))) : ∏ l ∈ T, h l ∈ (H.pow T.card).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleZExtend».«prod_mem_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZExtend_prod_mem_pow_64615a997730
