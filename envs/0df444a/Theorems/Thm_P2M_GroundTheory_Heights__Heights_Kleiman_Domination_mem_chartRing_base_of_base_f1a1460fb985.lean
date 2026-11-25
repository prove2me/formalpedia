-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_chartRing_base_of_base_f1a1460fb985
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_chartRing_base_of_base_f1a1460fb985
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:59:17.460641+00:00
-- url     : https://prove2.me/theorems/347d5052-9950-452b-9989-15f9a150f833
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Domination mem chart Ring base of base f1a1460fb985: P2 M Ground Theory Heights  Heights Kleiman Domination mem chart Ring base of base f1a1460fb985
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Domination mem chart Ring base of base f1a1460fb985 construction uses the P2 M Ground Theory Heights  Heights Kleiman Domination mem chart Ring base of base f1a1460fb985 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDomination.lean#L152-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDomination.lean#L152-L154

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_chartRing_base_of_base_f1a1460fb985 (z : Ω) (hz : z ∈ chartRing S x (singleChart hi)) :
    z ∈ chartRing (chartRing S x (singleChart hi)) x' (singleChart hj) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Domination».«mem_chartRing_base_of_base» := P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_chartRing_base_of_base_f1a1460fb985
