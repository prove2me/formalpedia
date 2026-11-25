-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_colPoly_eval_e4846f8558e5
-- name    : P2M_GroundTheory_Heights__Heights_FourB_colPoly_eval_e4846f8558e5
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:40:38.720248+00:00
-- url     : https://prove2.me/theorems/e87f68a0-b14e-492c-b5e3-fb93c4af80c6
-- title:
--   P2 M Ground Theory Heights  Heights Four B col Poly eval e4846f8558e5: P2 M Ground Theory Heights  Heights Four B col Poly eval e4846f8558e5
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B col Poly eval e4846f8558e5 construction uses the P2 M Ground Theory Heights  Heights Four B col Poly eval e4846f8558e5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/FlagPsDeriv.lean#L66-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/FlagPsDeriv.lean#L66-L73

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

theorem P2M_GroundTheory_Heights__Heights_FourB_colPoly_eval_e4846f8558e5 (u : LowerPair N → ℂ) (t : ℝ) :
    (colPoly i hi (lowerMatrix u)).map (evalRingHom (t : ℂ)) =
      ((1 : Matrix (Fin N) (Fin N) ℂ) + lowerMatrix (t • u)).submatrix id (Fin.castLE hi) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«colPoly_eval» := P2M_GroundTheory_Heights__Heights_FourB_colPoly_eval_e4846f8558e5
