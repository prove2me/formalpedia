-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LineBundle_tensor_toSubSystem_c7b278ca5880
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LineBundle_tensor_toSubSystem_c7b278ca5880
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:20:49.154+00:00
-- url     : https://prove2.me/theorems/55ac0c23-13de-51b7-9529-a98618c57642
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Line Bundle tensor to Sub System c7b278ca5880: P2 M Ground Theory Heights  Heights Kleiman Line Bundle tensor to Sub System c7b278ca5880
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Line Bundle tensor to Sub System c7b278ca5880 construction uses the P2 M Ground Theory Heights  Heights Kleiman Line Bundle tensor to Sub System c7b278ca5880 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistBundleToSubSystem.lean#L77-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistBundleToSubSystem.lean#L77-L78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LineBundle_tensor_toSubSystem_c7b278ca5880 (L L' : LineBundle S x) :
    (L.tensor L').toSubSystem = L.toSubSystem.twist L'.toSubSystem := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LineBundle».«tensor_toSubSystem» := P2M_GroundTheory_Heights__Heights_Kleiman_LineBundle_tensor_toSubSystem_c7b278ca5880
