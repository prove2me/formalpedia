-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZTwist_proof_28af41600539
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZTwist_proof_28af41600539
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:58:43.106803+00:00
-- url     : https://prove2.me/theorems/58f03b33-73dd-4f63-93c5-d6b3c2d93f0d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample ZTwist proof 28af41600539: P2 M Ground Theory Heights  Heights Kleiman Very Ample ZTwist proof 28af41600539
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample ZTwist proof 28af41600539 construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample ZTwist proof 28af41600539 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZTwist.lean#L69-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleZTwist.lean#L69-L157

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZTwistSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZFamilySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleTwistLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZTwist
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
open MvPolynomial
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZTwist
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZTwist_proof_28af41600539 (hFam : VeryAmpleZFamily.Statement.{u, v, w}) : VeryAmpleZTwist.Statement.{u, v, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleZTwist».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZTwist_proof_28af41600539
