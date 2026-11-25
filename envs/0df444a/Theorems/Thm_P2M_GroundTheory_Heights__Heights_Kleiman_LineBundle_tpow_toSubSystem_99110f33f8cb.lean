-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LineBundle_tpow_toSubSystem_99110f33f8cb
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LineBundle_tpow_toSubSystem_99110f33f8cb
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T06:21:10.493794+00:00
-- url     : https://prove2.me/theorems/847d2add-8207-555e-bff4-c9edae7d98a2
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Line Bundle tpow to Sub System 99110f33f8cb: P2 M Ground Theory Heights  Heights Kleiman Line Bundle tpow to Sub System 99110f33f8cb
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Line Bundle tpow to Sub System 99110f33f8cb construction uses the P2 M Ground Theory Heights  Heights Kleiman Line Bundle tpow to Sub System 99110f33f8cb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistBundleToSubSystem.lean#L84-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistBundleToSubSystem.lean#L84-L91

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LineBundle_tpow_toSubSystem_99110f33f8cb (L : LineBundle S x) (n : ℕ) :
    (L.tpow n).toSubSystem = L.toSubSystem.pow n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LineBundle».«tpow_toSubSystem» := P2M_GroundTheory_Heights__Heights_Kleiman_LineBundle_tpow_toSubSystem_99110f33f8cb
