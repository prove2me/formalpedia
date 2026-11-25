-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_rowPoly_eval_c3b96230d097
-- name    : P2M_GroundTheory_Heights__Heights_FourB_rowPoly_eval_c3b96230d097
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:40:05.836605+00:00
-- url     : https://prove2.me/theorems/f0aaeea2-79d4-5dd5-b6b2-7f3b84f5d82b
-- title:
--   P2 M Ground Theory Heights  Heights Four B row Poly eval c3b96230d097: P2 M Ground Theory Heights  Heights Four B row Poly eval c3b96230d097
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B row Poly eval c3b96230d097 construction uses the P2 M Ground Theory Heights  Heights Four B row Poly eval c3b96230d097 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/FlagPsDeriv.lean#L75-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/FlagPsDeriv.lean#L75-L88

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_FlagPsLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_FlagPsDeriv
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
variable {N : ℕ} (p i : ℕ) (hi : i ≤ N)

theorem P2M_GroundTheory_Heights__Heights_FourB_rowPoly_eval_c3b96230d097 (u : LowerPair N → ℂ) (t : ℝ) :
    (rowPoly i hi (lowerMatrix u)).map (evalRingHom (t : ℂ)) =
      (((1 : Matrix (Fin N) (Fin N) ℂ) + lowerMatrix (t • u)).submatrix id
        (Fin.castLE hi)).conjTranspose := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«rowPoly_eval» := P2M_GroundTheory_Heights__Heights_FourB_rowPoly_eval_c3b96230d097
