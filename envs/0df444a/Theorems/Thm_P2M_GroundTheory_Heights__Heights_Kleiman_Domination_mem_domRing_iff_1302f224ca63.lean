-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_domRing_iff_1302f224ca63
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_domRing_iff_1302f224ca63
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:21:36.827596+00:00
-- url     : https://prove2.me/theorems/6ef5d94e-6854-44da-b8e6-33083a71b7c6
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Domination mem dom Ring iff 1302f224ca63: P2 M Ground Theory Heights  Heights Kleiman Domination mem dom Ring iff 1302f224ca63
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Domination mem dom Ring iff 1302f224ca63 construction uses the P2 M Ground Theory Heights  Heights Kleiman Domination mem dom Ring iff 1302f224ca63 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDomination.lean#L218-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDomination.lean#L218-L233

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_domRing_iff_1302f224ca63 (b : Ω) : b ∈ domRing S x x' i ↔
    ∀ J : Chart x', b ∈ chartRing (chartRing S x (singleChart hi)) x' J := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Domination».«mem_domRing_iff» := P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_domRing_iff_1302f224ca63
