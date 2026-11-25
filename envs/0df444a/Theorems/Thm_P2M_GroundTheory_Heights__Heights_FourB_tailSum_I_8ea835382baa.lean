-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_tailSum_I_8ea835382baa
-- name    : P2M_GroundTheory_Heights__Heights_FourB_tailSum_I_8ea835382baa
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:46:36.262801+00:00
-- url     : https://prove2.me/theorems/72d78726-9fbc-4c15-89c5-8fc10e912726
-- title:
--   P2 M Ground Theory Heights  Heights Four B tail Sum I 8ea835382baa: P2 M Ground Theory Heights  Heights Four B tail Sum I 8ea835382baa
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B tail Sum I 8ea835382baa construction uses the P2 M Ground Theory Heights  Heights Four B tail Sum I 8ea835382baa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PFlagWeightLevi.lean#L36-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PFlagWeightLevi.lean#L36-L42

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

theorem P2M_GroundTheory_Heights__Heights_FourB_tailSum_I_8ea835382baa {N : ℕ} (p i : ℕ) (u : LowerPair N → ℂ) :
    tailSum p i (lowerMatrix (Complex.I • u)) = tailSum p i (lowerMatrix u) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«tailSum_I» := P2M_GroundTheory_Heights__Heights_FourB_tailSum_I_8ea835382baa
