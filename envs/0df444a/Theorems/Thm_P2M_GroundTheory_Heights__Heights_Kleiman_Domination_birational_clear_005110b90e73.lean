-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_birational_clear_005110b90e73
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Domination_birational_clear_005110b90e73
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:56:17.871511+00:00
-- url     : https://prove2.me/theorems/2409d46a-58d4-405e-a12f-a0a9a6de1283
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Domination birational clear 005110b90e73: P2 M Ground Theory Heights  Heights Kleiman Domination birational clear 005110b90e73
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Domination birational clear 005110b90e73 construction uses the P2 M Ground Theory Heights  Heights Kleiman Domination birational clear 005110b90e73 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDomination.lean#L326-L347
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDomination.lean#L326-L347

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Domination_birational_clear_005110b90e73 (hbir : IsBirationalPt S x) {i : Fin (N + 1)} (hi : x i ≠ 0) (g : Ω) :
    ∃ d ∈ {y | ∃ (f : Poly S N) (e : ℕ), f.IsHomogeneous e ∧ aeval x f ≠ 0 ∧ aeval x f / x i ^ e = y},
      d * g ∈ chartRing S x (singleChart hi) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Domination».«birational_clear» := P2M_GroundTheory_Heights__Heights_Kleiman_Domination_birational_clear_005110b90e73
