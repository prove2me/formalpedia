-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_div_mem_of_mem_pullPow_8800596b5cce
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Domination_div_mem_of_mem_pullPow_8800596b5cce
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:59:20.633062+00:00
-- url     : https://prove2.me/theorems/abf9edcf-8989-4f87-9e05-2cd877e75734
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Domination div mem of mem pull Pow 8800596b5cce: P2 M Ground Theory Heights  Heights Kleiman Domination div mem of mem pull Pow 8800596b5cce
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Domination div mem of mem pull Pow 8800596b5cce construction uses the P2 M Ground Theory Heights  Heights Kleiman Domination div mem of mem pull Pow 8800596b5cce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDomination.lean#L156-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PDomination.lean#L156-L184

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Domination_div_mem_of_mem_pullPow_8800596b5cce : ∀ (n : ℕ) {y : Ω}, y ∈ pullPow (S := S) x x' n (singleChart hj) →
    y / x i ^ n ∈ chartRing (chartRing S x (singleChart hi)) x' (singleChart hj)
  := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Domination».«div_mem_of_mem_pullPow» := P2M_GroundTheory_Heights__Heights_Kleiman_Domination_div_mem_of_mem_pullPow_8800596b5cce
