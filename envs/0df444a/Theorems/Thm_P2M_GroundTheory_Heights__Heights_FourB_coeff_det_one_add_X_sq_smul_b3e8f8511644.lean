-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_coeff_det_one_add_X_sq_smul_b3e8f8511644
-- name    : P2M_GroundTheory_Heights__Heights_FourB_coeff_det_one_add_X_sq_smul_b3e8f8511644
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:34:22.679803+00:00
-- url     : https://prove2.me/theorems/05c376d2-7e64-448b-9faa-7d48f454047c
-- title:
--   P2 M Ground Theory Heights  Heights Four B coeff det one add X sq smul b3e8f8511644: P2 M Ground Theory Heights  Heights Four B coeff det one add X sq smul b3e8f8511644
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B coeff det one add X sq smul b3e8f8511644 construction uses the P2 M Ground Theory Heights  Heights Four B coeff det one add X sq smul b3e8f8511644 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/FlagPsLine.lean#L160-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/FlagPsLine.lean#L160-L165

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

theorem P2M_GroundTheory_Heights__Heights_FourB_coeff_det_one_add_X_sq_smul_b3e8f8511644 {n : Type*} [Fintype n] [DecidableEq n]
    (K : Matrix n n ℂ[X]) :
    (1 + (X ^ 2 : ℂ[X]) • K).det.coeff 0 = 1 ∧ (1 + (X ^ 2 : ℂ[X]) • K).det.coeff 1 = 0 ∧
      (1 + (X ^ 2 : ℂ[X]) • K).det.coeff 2 = K.trace.coeff 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«coeff_det_one_add_X_sq_smul» := P2M_GroundTheory_Heights__Heights_FourB_coeff_det_one_add_X_sq_smul_b3e8f8511644
