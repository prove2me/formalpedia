-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LineBundle_powBundle_toSubSystem_418f6a814041
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LineBundle_powBundle_toSubSystem_418f6a814041
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:06:06.056275+00:00
-- url     : https://prove2.me/theorems/5deccf77-8426-59fb-99eb-a9ea601d9590
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Line Bundle pow Bundle to Sub System 418f6a814041: P2 M Ground Theory Heights  Heights Kleiman Line Bundle pow Bundle to Sub System 418f6a814041
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Line Bundle pow Bundle to Sub System 418f6a814041 construction uses the P2 M Ground Theory Heights  Heights Kleiman Line Bundle pow Bundle to Sub System 418f6a814041 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistAlg.lean#L155-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistAlg.lean#L155-L161

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
open GroundTheory.Heights₂.Heights.Kleiman.LineBundle

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LineBundle_powBundle_toSubSystem_418f6a814041 (Q : LineBundle S x) (n : ℕ) :
    (Q.powBundle n).toSubSystem = Q.toSubSystem.pow n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LineBundle».«powBundle_toSubSystem» := P2M_GroundTheory_Heights__Heights_Kleiman_LineBundle_powBundle_toSubSystem_418f6a814041
