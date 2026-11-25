-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_sigTop_mul_self_5c5b61b99b20
-- name    : P2M_GroundTheory_Heights__Heights_FourB_sigTop_mul_self_5c5b61b99b20
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:35:00.968015+00:00
-- url     : https://prove2.me/theorems/f3a81bff-4b82-40c2-9ed1-1f3c21d2b1b9
-- title:
--   P2 M Ground Theory Heights  Heights Four B sig Top mul self 5c5b61b99b20: P2 M Ground Theory Heights  Heights Four B sig Top mul self 5c5b61b99b20
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B sig Top mul self 5c5b61b99b20 construction uses the P2 M Ground Theory Heights  Heights Four B sig Top mul self 5c5b61b99b20 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/FlagPsLine.lean#L98-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/FlagPsLine.lean#L98-L103

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

theorem P2M_GroundTheory_Heights__Heights_FourB_sigTop_mul_self_5c5b61b99b20 : sigTop p i hi * sigTop p i hi = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«sigTop_mul_self» := P2M_GroundTheory_Heights__Heights_FourB_sigTop_mul_self_5c5b61b99b20
