-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_sum_fin_telescope_d731859c771b
-- name    : P2M_GroundTheory_Heights__Heights_FourB_sum_fin_telescope_d731859c771b
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:46:04.211734+00:00
-- url     : https://prove2.me/theorems/b8b96bef-5335-5f1c-879d-e0396f3c7e20
-- title:
--   P2 M Ground Theory Heights  Heights Four B sum fin telescope d731859c771b: P2 M Ground Theory Heights  Heights Four B sum fin telescope d731859c771b
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B sum fin telescope d731859c771b construction uses the P2 M Ground Theory Heights  Heights Four B sum fin telescope d731859c771b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PFlagWeightLevi.lean#L74-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PFlagWeightLevi.lean#L74-L84

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_FlagPsDeriv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PFlagWeightLevi
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
open ReciprocityTheory.AnForm
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_FourB_sum_fin_telescope_d731859c771b {N : ℕ} (Λ : ℕ → ℝ) (b c : ℕ) (hbc : b < c) (hc : c ≤ N) :
    ∑ k : Fin N, (if b ≤ k.val ∧ k.val < c then Λ k - Λ (k.val + 1) else 0) = Λ b - Λ c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«sum_fin_telescope» := P2M_GroundTheory_Heights__Heights_FourB_sum_fin_telescope_d731859c771b
