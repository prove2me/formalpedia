-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_deriv_deriv_flagPs_738815f19103
-- name    : P2M_GroundTheory_Heights__Heights_FourB_deriv_deriv_flagPs_738815f19103
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:40:43.706833+00:00
-- url     : https://prove2.me/theorems/38621986-3344-49c5-b36e-d8cba2cf92a1
-- title:
--   P2 M Ground Theory Heights  Heights Four B deriv deriv flag Ps 738815f19103: P2 M Ground Theory Heights  Heights Four B deriv deriv flag Ps 738815f19103
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B deriv deriv flag Ps 738815f19103 construction uses the P2 M Ground Theory Heights  Heights Four B deriv deriv flag Ps 738815f19103 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/FlagPsDeriv.lean#L116-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/FlagPsDeriv.lean#L116-L120

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

theorem P2M_GroundTheory_Heights__Heights_FourB_deriv_deriv_flagPs_738815f19103 (u : LowerPair N → ℂ) :
    deriv (deriv fun t : ℝ => flagPs N p i hi (t • u)) 0 = 2 * tailSum p i (lowerMatrix u) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«deriv_deriv_flagPs» := P2M_GroundTheory_Heights__Heights_FourB_deriv_deriv_flagPs_738815f19103
