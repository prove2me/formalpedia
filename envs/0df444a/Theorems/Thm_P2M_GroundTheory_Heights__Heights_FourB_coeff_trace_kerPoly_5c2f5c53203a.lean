-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_coeff_trace_kerPoly_5c2f5c53203a
-- name    : P2M_GroundTheory_Heights__Heights_FourB_coeff_trace_kerPoly_5c2f5c53203a
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:40:52.419613+00:00
-- url     : https://prove2.me/theorems/01ae2c39-9883-59fb-b238-6684942a02cb
-- title:
--   P2 M Ground Theory Heights  Heights Four B coeff trace ker Poly 5c2f5c53203a: P2 M Ground Theory Heights  Heights Four B coeff trace ker Poly 5c2f5c53203a
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B coeff trace ker Poly 5c2f5c53203a construction uses the P2 M Ground Theory Heights  Heights Four B coeff trace ker Poly 5c2f5c53203a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/FlagPsDeriv.lean#L18-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/FlagPsDeriv.lean#L18-L35

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

theorem P2M_GroundTheory_Heights__Heights_FourB_coeff_trace_kerPoly_5c2f5c53203a (L : Matrix (Fin N) (Fin N) ℂ) :
    (kerPoly p i hi L).trace.coeff 0 = (sigTop p i hi * tailForm p i hi L).trace := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«coeff_trace_kerPoly» := P2M_GroundTheory_Heights__Heights_FourB_coeff_trace_kerPoly_5c2f5c53203a
