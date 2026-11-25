-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_levi_finset_sum_e74cda080f38
-- name    : P2M_GroundTheory_Heights__Heights_FourB_levi_finset_sum_e74cda080f38
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:17:47.148797+00:00
-- url     : https://prove2.me/theorems/1bf43c2c-9d8a-4201-b71b-fe68d8609afc
-- title:
--   P2 M Ground Theory Heights  Heights Four B levi finset sum e74cda080f38: P2 M Ground Theory Heights  Heights Four B levi finset sum e74cda080f38
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B levi finset sum e74cda080f38 construction uses the P2 M Ground Theory Heights  Heights Four B levi finset sum e74cda080f38 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/LeviLine.lean#L41-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/LeviLine.lean#L41-L57

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm Filter Topology Polynomial
noncomputable section
variable {ι : Type*} [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_FourB_levi_finset_sum_e74cda080f38 {κ : Type*} (s : Finset κ) (F : κ → (ι → ℂ) → ℝ)
    (hF : ∀ j ∈ s, ContDiffAt ℝ 2 (F j) 0) (w : ι → ℂ) :
    levi (fun z => ∑ j ∈ s, F j z) 0 w = ∑ j ∈ s, levi (F j) 0 w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«levi_finset_sum» := P2M_GroundTheory_Heights__Heights_FourB_levi_finset_sum_e74cda080f38
