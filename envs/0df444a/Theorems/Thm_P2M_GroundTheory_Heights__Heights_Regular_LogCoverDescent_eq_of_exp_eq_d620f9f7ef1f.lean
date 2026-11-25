-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_eq_of_exp_eq_d620f9f7ef1f
-- name    : P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_eq_of_exp_eq_d620f9f7ef1f
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:17:33.179827+00:00
-- url     : https://prove2.me/theorems/4a29ed27-f7c1-41ac-a898-1c28a4b78bb3
-- title:
--   P2 M Ground Theory Heights  Heights Regular Log Cover Descent eq of exp eq d620f9f7ef1f: P2 M Ground Theory Heights  Heights Regular Log Cover Descent eq of exp eq d620f9f7ef1f
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Log Cover Descent eq of exp eq d620f9f7ef1f construction uses the P2 M Ground Theory Heights  Heights Regular Log Cover Descent eq of exp eq d620f9f7ef1f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PLogCoverDescent.lean#L83-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PLogCoverDescent.lean#L83-L96

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StLogCoverDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PLogCoverDescent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.LogCoverDescent
variable {n a : ℕ} (h : a ≤ n)
variable {h}

theorem P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_eq_of_exp_eq_d620f9f7ef1f {φ : (Fin n → ℂ) → ℂ} (hφ : ∀ (i : Fin a), ∀ w ∈ logCover h,
      φ (w + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I)) = φ w) {w w' : Fin n → ℂ}
    (hw : w ∈ logCover h)
    (hd : ∀ k : Fin n, (k.val < a → Complex.exp (w' k) = Complex.exp (w k)) ∧
      (a ≤ k.val → w' k = w k)) :
    φ w' = φ w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«LogCoverDescent».«eq_of_exp_eq» := P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_eq_of_exp_eq_d620f9f7ef1f
