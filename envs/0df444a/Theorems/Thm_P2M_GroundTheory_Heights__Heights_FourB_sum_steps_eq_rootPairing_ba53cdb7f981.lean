-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_sum_steps_eq_rootPairing_ba53cdb7f981
-- name    : P2M_GroundTheory_Heights__Heights_FourB_sum_steps_eq_rootPairing_ba53cdb7f981
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:46:58.184708+00:00
-- url     : https://prove2.me/theorems/1190607e-70f7-4446-bdcf-e9a17fd30f62
-- title:
--   P2 M Ground Theory Heights  Heights Four B sum steps eq root Pairing ba53cdb7f981: P2 M Ground Theory Heights  Heights Four B sum steps eq root Pairing ba53cdb7f981
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B sum steps eq root Pairing ba53cdb7f981 construction uses the P2 M Ground Theory Heights  Heights Four B sum steps eq root Pairing ba53cdb7f981 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PFlagWeightLevi.lean#L86-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PFlagWeightLevi.lean#L86-L142

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

theorem P2M_GroundTheory_Heights__Heights_FourB_sum_steps_eq_rootPairing_ba53cdb7f981 (N p : ℕ) (lam : Fin N → ℝ) (u : LowerPair N → ℂ) :
    ∑ k : Fin N, (if h : k.val + 1 < N then
      (lam k - lam ⟨k.val + 1, h⟩) * tailSum p (k.val + 1) (lowerMatrix u) else 0) =
      ∑ q : LowerPair N, rootPairing N p lam q * ‖u q‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«sum_steps_eq_rootPairing» := P2M_GroundTheory_Heights__Heights_FourB_sum_steps_eq_rootPairing_ba53cdb7f981
