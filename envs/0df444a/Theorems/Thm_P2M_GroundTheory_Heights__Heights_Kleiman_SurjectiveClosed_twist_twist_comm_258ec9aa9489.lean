-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_twist_twist_comm_258ec9aa9489
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_twist_twist_comm_258ec9aa9489
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:23:05.470854+00:00
-- url     : https://prove2.me/theorems/ac4f4954-9f4c-5011-9a67-f8346d1b963e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Surjective Closed twist twist comm 258ec9aa9489: P2 M Ground Theory Heights  Heights Kleiman Surjective Closed twist twist comm 258ec9aa9489
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Surjective Closed twist twist comm 258ec9aa9489 construction uses the P2 M Ground Theory Heights  Heights Kleiman Surjective Closed twist twist comm 258ec9aa9489 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSurjectiveClosed.lean#L110-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSurjectiveClosed.lean#L110-L112

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsIdealTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSurjectiveClosed
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
open GroundTheory.Heights₂.Heights.Kleiman.SurjectiveClosed
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_twist_twist_comm_258ec9aa9489 (F Q R : SubSystem S x Ω) : (F.twist Q).twist R = (F.twist R).twist Q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SurjectiveClosed».«twist_twist_comm» := P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_twist_twist_comm_258ec9aa9489
