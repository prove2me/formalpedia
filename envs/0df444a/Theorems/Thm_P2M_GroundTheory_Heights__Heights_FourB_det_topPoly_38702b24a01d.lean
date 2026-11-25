-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_det_topPoly_38702b24a01d
-- name    : P2M_GroundTheory_Heights__Heights_FourB_det_topPoly_38702b24a01d
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:33:55.046164+00:00
-- url     : https://prove2.me/theorems/dea5f79d-3d91-5240-a427-3b6c6f5e7208
-- title:
--   P2 M Ground Theory Heights  Heights Four B det top Poly 38702b24a01d: P2 M Ground Theory Heights  Heights Four B det top Poly 38702b24a01d
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B det top Poly 38702b24a01d construction uses the P2 M Ground Theory Heights  Heights Four B det top Poly 38702b24a01d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/FlagPsLine.lean#L107-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/FlagPsLine.lean#L107-L118

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_FlagPsLine
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
open Polynomial Matrix
noncomputable section
variable {N : ℕ}
variable (p i : ℕ) (hi : i ≤ N) (L : Matrix (Fin N) (Fin N) ℂ)
variable {L}

theorem P2M_GroundTheory_Heights__Heights_FourB_det_topPoly_38702b24a01d (hL : ∀ a b : Fin N, ¬ b < a → L a b = 0) : (topPoly i hi L).det = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«det_topPoly» := P2M_GroundTheory_Heights__Heights_FourB_det_topPoly_38702b24a01d
