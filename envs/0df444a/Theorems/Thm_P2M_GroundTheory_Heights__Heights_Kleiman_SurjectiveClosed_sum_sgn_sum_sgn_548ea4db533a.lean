-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_sum_sgn_sum_sgn_548ea4db533a
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_sum_sgn_sum_sgn_548ea4db533a
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:23:27.391863+00:00
-- url     : https://prove2.me/theorems/8a120bdf-cb8b-4bef-9e32-4fbc2492db1d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Surjective Closed sum sgn sum sgn 548ea4db533a: P2 M Ground Theory Heights  Heights Kleiman Surjective Closed sum sgn sum sgn 548ea4db533a
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Surjective Closed sum sgn sum sgn 548ea4db533a construction uses the P2 M Ground Theory Heights  Heights Kleiman Surjective Closed sum sgn sum sgn 548ea4db533a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSurjectiveClosed.lean#L54-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSurjectiveClosed.lean#L54-L88

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
variable {n : ℕ}
variable {U : Finset (Fin n)} {A : Type*} [AddCommGroup A]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_sum_sgn_sum_sgn_548ea4db533a (φ : Cell U → A) (L : Cech.Idx U 2) :
    ∑ j : L.1.1, Cech.sgn L.1.1 j • ∑ k : (Cech.face L j).1.1,
      Cech.sgn (Cech.face L j).1.1 k • φ (Cech.face (Cech.face L j) k).1 = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SurjectiveClosed».«sum_sgn_sum_sgn» := P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_sum_sgn_sum_sgn_548ea4db533a
