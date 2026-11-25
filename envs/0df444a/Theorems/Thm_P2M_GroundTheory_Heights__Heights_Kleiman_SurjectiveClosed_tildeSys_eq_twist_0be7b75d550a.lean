-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_tildeSys_eq_twist_0be7b75d550a
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_tildeSys_eq_twist_0be7b75d550a
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:23:17.824797+00:00
-- url     : https://prove2.me/theorems/64662416-7134-49d1-873a-4101d3207d7f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Surjective Closed tilde Sys eq twist 0be7b75d550a: P2 M Ground Theory Heights  Heights Kleiman Surjective Closed tilde Sys eq twist 0be7b75d550a
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Surjective Closed tilde Sys eq twist 0be7b75d550a construction uses the P2 M Ground Theory Heights  Heights Kleiman Surjective Closed tilde Sys eq twist 0be7b75d550a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSurjectiveClosed.lean#L132-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSurjectiveClosed.lean#L132-L181

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_tildeSys_eq_twist_0be7b75d550a (M : FinGradedSub (S := S) (x := x) Ω) (c : ℤ) :
    M.tildeSys c = (M.tildeSys 0).twist (twistSys S x c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SurjectiveClosed».«tildeSys_eq_twist» := P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_tildeSys_eq_twist_0be7b75d550a
