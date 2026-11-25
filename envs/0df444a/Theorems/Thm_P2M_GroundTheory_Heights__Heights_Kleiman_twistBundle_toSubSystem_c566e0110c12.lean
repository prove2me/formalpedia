-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistBundle_toSubSystem_c566e0110c12
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_twistBundle_toSubSystem_c566e0110c12
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:20:41.863137+00:00
-- url     : https://prove2.me/theorems/97213ee6-bb39-529a-90eb-b1377b921501
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman twist Bundle to Sub System c566e0110c12: P2 M Ground Theory Heights  Heights Kleiman twist Bundle to Sub System c566e0110c12
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman twist Bundle to Sub System c566e0110c12 construction uses the P2 M Ground Theory Heights  Heights Kleiman twist Bundle to Sub System c566e0110c12 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistBundleToSubSystem.lean#L93-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistBundleToSubSystem.lean#L93-L93

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_twistBundle_toSubSystem_c566e0110c12 (c : ℤ) : (twistBundle S x c).toSubSystem = twistSys S x c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«twistBundle_toSubSystem» := P2M_GroundTheory_Heights__Heights_Kleiman_twistBundle_toSubSystem_c566e0110c12
