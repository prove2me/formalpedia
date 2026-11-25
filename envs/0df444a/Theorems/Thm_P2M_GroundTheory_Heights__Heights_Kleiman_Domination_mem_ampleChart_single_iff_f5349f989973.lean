-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_ampleChart_single_iff_f5349f989973
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_ampleChart_single_iff_f5349f989973
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:09:56.434233+00:00
-- url     : https://prove2.me/theorems/830bdfcf-4096-4982-9088-5bd7f023bdce
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Domination mem ample Chart single iff f5349f989973: P2 M Ground Theory Heights  Heights Kleiman Domination mem ample Chart single iff f5349f989973
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Domination mem ample Chart single iff f5349f989973 construction uses the P2 M Ground Theory Heights  Heights Kleiman Domination mem ample Chart single iff f5349f989973 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDomination.lean#L186-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDomination.lean#L186-L216

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_ampleChart_single_iff_f5349f989973 (a : Ω) :
    a ∈ ampleChart (pullSys (S := S) x x') 1 (x i) (singleChart hj) ↔
      a ∈ chartRing (chartRing S x (singleChart hi)) x' (singleChart hj) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Domination».«mem_ampleChart_single_iff» := P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_ampleChart_single_iff_f5349f989973
