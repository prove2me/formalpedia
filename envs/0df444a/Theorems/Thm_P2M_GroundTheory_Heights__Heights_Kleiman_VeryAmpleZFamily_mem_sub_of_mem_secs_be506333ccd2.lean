-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFamily_mem_sub_of_mem_secs_be506333ccd2
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFamily_mem_sub_of_mem_secs_be506333ccd2
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:03:51.952986+00:00
-- url     : https://prove2.me/theorems/af3ce7c7-2f24-5e4c-ac07-c54ded1fa785
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample ZFamily mem sub of mem secs be506333ccd2: P2 M Ground Theory Heights  Heights Kleiman Very Ample ZFamily mem sub of mem secs be506333ccd2
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample ZFamily mem sub of mem secs be506333ccd2 construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample ZFamily mem sub of mem secs be506333ccd2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZFamily.lean#L62-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZFamily.lean#L62-L63

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFamily_mem_sub_of_mem_secs_be506333ccd2 {H : SubSystem S x Ω} {z : Ω} (hz : z ∈ H.secs) (I : Chart x) : z ∈ H.sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleZFamily».«mem_sub_of_mem_secs» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZFamily_mem_sub_of_mem_secs_be506333ccd2
