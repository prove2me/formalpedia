-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_twist_comm_31b97c8bd736
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_twist_comm_31b97c8bd736
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:08:03.044477+00:00
-- url     : https://prove2.me/theorems/35263481-a341-4c9c-a329-464404dcb7a0
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sub System twist comm 31b97c8bd736: P2 M Ground Theory Heights  Heights Kleiman Sub System twist comm 31b97c8bd736
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sub System twist comm 31b97c8bd736 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sub System twist comm 31b97c8bd736 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistAlg.lean#L30-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistAlg.lean#L30-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
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
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
open GroundTheory.Heights₂.Heights.Kleiman.SubSystem

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_twist_comm_31b97c8bd736 (F Q : SubSystem S x Ω) : F.twist Q = Q.twist F := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SubSystem».«twist_comm» := P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_twist_comm_31b97c8bd736
