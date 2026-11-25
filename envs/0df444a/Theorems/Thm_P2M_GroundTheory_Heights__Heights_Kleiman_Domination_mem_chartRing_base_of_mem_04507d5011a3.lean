-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_chartRing_base_of_mem_04507d5011a3
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_chartRing_base_of_mem_04507d5011a3
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:00:10.079862+00:00
-- url     : https://prove2.me/theorems/01944ac4-a988-533e-aa76-c4344b9406e1
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Domination mem chart Ring base of mem 04507d5011a3: P2 M Ground Theory Heights  Heights Kleiman Domination mem chart Ring base of mem 04507d5011a3
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Domination mem chart Ring base of mem 04507d5011a3 construction uses the P2 M Ground Theory Heights  Heights Kleiman Domination mem chart Ring base of mem 04507d5011a3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDomination.lean#L138-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDomination.lean#L138-L150

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_chartRing_base_of_mem_04507d5011a3 (z : Ω) (hz : z ∈ chartRing S x' (singleChart hj)) :
    z ∈ chartRing (chartRing S x (singleChart hi)) x' (singleChart hj) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Domination».«mem_chartRing_base_of_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_chartRing_base_of_mem_04507d5011a3
