-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_fg_domSub_2df31f735772
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Domination_fg_domSub_2df31f735772
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:21:46.125499+00:00
-- url     : https://prove2.me/theorems/9393380a-84a6-407e-b40f-5e10bae52283
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Domination fg dom Sub 2df31f735772: P2 M Ground Theory Heights  Heights Kleiman Domination fg dom Sub 2df31f735772
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Domination fg dom Sub 2df31f735772 construction uses the P2 M Ground Theory Heights  Heights Kleiman Domination fg dom Sub 2df31f735772 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDomination.lean#L250-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDomination.lean#L250-L259

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDomination
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
open GroundTheory.Heights₂.Heights.Kleiman.Domination
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N N' : ℕ}
  {x : Fin (N + 1) → Ω} {x' : Fin (N' + 1) → Ω}
variable {i : Fin (N + 1)} (hi : x i ≠ 0) {j : Fin (N' + 1)} (hj : x' j ≠ 0)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Domination_fg_domSub_2df31f735772 [IsNoetherianRing S] (hF : FiniteSections.Statement.{w, w}) (hx' : x' ≠ 0) :
    (Subalgebra.toSubmodule (domSub (S := S) x' hi)).FG := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Domination».«fg_domSub» := P2M_GroundTheory_Heights__Heights_Kleiman_Domination_fg_domSub_2df31f735772
