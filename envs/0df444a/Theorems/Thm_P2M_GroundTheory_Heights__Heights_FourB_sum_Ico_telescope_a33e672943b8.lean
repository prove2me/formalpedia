-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_sum_Ico_telescope_a33e672943b8
-- name    : P2M_GroundTheory_Heights__Heights_FourB_sum_Ico_telescope_a33e672943b8
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:46:36.723134+00:00
-- url     : https://prove2.me/theorems/a7c2f57b-8bba-405c-ae2e-05dd498053df
-- title:
--   P2 M Ground Theory Heights  Heights Four B sum Ico telescope a33e672943b8: P2 M Ground Theory Heights  Heights Four B sum Ico telescope a33e672943b8
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B sum Ico telescope a33e672943b8 construction uses the P2 M Ground Theory Heights  Heights Four B sum Ico telescope a33e672943b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PFlagWeightLevi.lean#L66-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PFlagWeightLevi.lean#L66-L72

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

theorem P2M_GroundTheory_Heights__Heights_FourB_sum_Ico_telescope_a33e672943b8 (Λ : ℕ → ℝ) (b m : ℕ) :
    ∑ k ∈ Finset.Ico b (b + m), (Λ k - Λ (k + 1)) = Λ b - Λ (b + m) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«sum_Ico_telescope» := P2M_GroundTheory_Heights__Heights_FourB_sum_Ico_telescope_a33e672943b8
