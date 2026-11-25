-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_norm_det_sigTop_d1ab7a11e30b
-- name    : P2M_GroundTheory_Heights__Heights_FourB_norm_det_sigTop_d1ab7a11e30b
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:41:25.514133+00:00
-- url     : https://prove2.me/theorems/e963addf-1f61-45d1-adab-f83c8254a346
-- title:
--   P2 M Ground Theory Heights  Heights Four B norm det sig Top d1ab7a11e30b: P2 M Ground Theory Heights  Heights Four B norm det sig Top d1ab7a11e30b
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B norm det sig Top d1ab7a11e30b construction uses the P2 M Ground Theory Heights  Heights Four B norm det sig Top d1ab7a11e30b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/FlagPsDeriv.lean#L105-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/FlagPsDeriv.lean#L105-L109

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

theorem P2M_GroundTheory_Heights__Heights_FourB_norm_det_sigTop_d1ab7a11e30b : ‖(sigTop p i hi).det‖ = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«norm_det_sigTop» := P2M_GroundTheory_Heights__Heights_FourB_norm_det_sigTop_d1ab7a11e30b
