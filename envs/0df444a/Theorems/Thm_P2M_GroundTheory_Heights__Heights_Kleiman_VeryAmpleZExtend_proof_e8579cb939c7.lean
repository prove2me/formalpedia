-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZExtend_proof_e8579cb939c7
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZExtend_proof_e8579cb939c7
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:31:50.572177+00:00
-- url     : https://prove2.me/theorems/d30b3b90-b8be-5a60-8748-52c00ae99a27
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample ZExtend proof e8579cb939c7: P2 M Ground Theory Heights  Heights Kleiman Very Ample ZExtend proof e8579cb939c7
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample ZExtend proof e8579cb939c7 construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample ZExtend proof e8579cb939c7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZExtend.lean#L73-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZExtend.lean#L73-L138

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsVeryAmpleZFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZExtend
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_proof_1c887bca4a14
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_proof_820eda5b4c8e

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZExtend_proof_e8579cb939c7 : VeryAmpleZExtend.Statement.{u, v, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleZExtend».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZExtend_proof_e8579cb939c7
