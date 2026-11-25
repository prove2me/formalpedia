-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistSys_twist_twistSys_37653a5a4181
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_twistSys_twist_twistSys_37653a5a4181
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:21:34.513825+00:00
-- url     : https://prove2.me/theorems/08b489e5-f976-4ed6-8f72-380721b89a4c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman twist Sys twist twist Sys 37653a5a4181: P2 M Ground Theory Heights  Heights Kleiman twist Sys twist twist Sys 37653a5a4181
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman twist Sys twist twist Sys 37653a5a4181 construction uses the P2 M Ground Theory Heights  Heights Kleiman twist Sys twist twist Sys 37653a5a4181 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistBundleToSubSystem.lean#L95-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistBundleToSubSystem.lean#L95-L103

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_twistSys_twist_twistSys_37653a5a4181 (a b : ℤ) :
    (twistSys S x a).twist (twistSys S x b) = twistSys S x (a + b) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«twistSys_twist_twistSys» := P2M_GroundTheory_Heights__Heights_Kleiman_twistSys_twist_twistSys_37653a5a4181
