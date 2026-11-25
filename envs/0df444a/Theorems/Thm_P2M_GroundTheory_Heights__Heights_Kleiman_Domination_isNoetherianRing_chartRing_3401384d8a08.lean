-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_isNoetherianRing_chartRing_3401384d8a08
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Domination_isNoetherianRing_chartRing_3401384d8a08
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:21:27.512061+00:00
-- url     : https://prove2.me/theorems/c12baea1-686c-4d9c-8a74-c413e1e8a398
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Domination is Noetherian Ring chart Ring 3401384d8a08: P2 M Ground Theory Heights  Heights Kleiman Domination is Noetherian Ring chart Ring 3401384d8a08
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Domination is Noetherian Ring chart Ring 3401384d8a08 construction uses the P2 M Ground Theory Heights  Heights Kleiman Domination is Noetherian Ring chart Ring 3401384d8a08 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDomination.lean#L126-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDomination.lean#L126-L134

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Domination_isNoetherianRing_chartRing_3401384d8a08 [IsNoetherianRing S] {i : Fin (N + 1)} (hi : x i ≠ 0) :
    IsNoetherianRing (chartRing S x (singleChart hi)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Domination».«isNoetherianRing_chartRing» := P2M_GroundTheory_Heights__Heights_Kleiman_Domination_isNoetherianRing_chartRing_3401384d8a08
