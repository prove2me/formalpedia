-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_det_flag_eval_f8bc5d8ce1ab
-- name    : P2M_GroundTheory_Heights__Heights_FourB_det_flag_eval_f8bc5d8ce1ab
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:41:19.670398+00:00
-- url     : https://prove2.me/theorems/6f43fa9f-3212-4534-9a5e-2c86269ec8be
-- title:
--   P2 M Ground Theory Heights  Heights Four B det flag eval f8bc5d8ce1ab: P2 M Ground Theory Heights  Heights Four B det flag eval f8bc5d8ce1ab
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B det flag eval f8bc5d8ce1ab construction uses the P2 M Ground Theory Heights  Heights Four B det flag eval f8bc5d8ce1ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/FlagPsDeriv.lean#L90-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/FlagPsDeriv.lean#L90-L103

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

theorem P2M_GroundTheory_Heights__Heights_FourB_det_flag_eval_f8bc5d8ce1ab (u : LowerPair N → ℂ) (t : ℝ) :
    ((((1 : Matrix (Fin N) (Fin N) ℂ) + lowerMatrix (t • u)).submatrix id
        (Fin.castLE hi)).conjTranspose * signatureForm N p *
        ((1 + lowerMatrix (t • u)).submatrix id (Fin.castLE hi))).det =
      (sigTop p i hi).det *
        ((1 + (X ^ 2 : ℂ[X]) • kerPoly p i hi (lowerMatrix u)).det).eval (t : ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«det_flag_eval» := P2M_GroundTheory_Heights__Heights_FourB_det_flag_eval_f8bc5d8ce1ab
