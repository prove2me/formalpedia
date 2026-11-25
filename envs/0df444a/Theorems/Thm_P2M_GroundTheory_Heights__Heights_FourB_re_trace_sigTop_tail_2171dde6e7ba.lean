-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_re_trace_sigTop_tail_2171dde6e7ba
-- name    : P2M_GroundTheory_Heights__Heights_FourB_re_trace_sigTop_tail_2171dde6e7ba
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:40:44.749946+00:00
-- url     : https://prove2.me/theorems/56ac2d5c-a5be-485a-a9cd-8d586c573609
-- title:
--   P2 M Ground Theory Heights  Heights Four B re trace sig Top tail 2171dde6e7ba: P2 M Ground Theory Heights  Heights Four B re trace sig Top tail 2171dde6e7ba
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B re trace sig Top tail 2171dde6e7ba construction uses the P2 M Ground Theory Heights  Heights Four B re trace sig Top tail 2171dde6e7ba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/FlagPsDeriv.lean#L37-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/FlagPsDeriv.lean#L37-L64

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

theorem P2M_GroundTheory_Heights__Heights_FourB_re_trace_sigTop_tail_2171dde6e7ba (L : Matrix (Fin N) (Fin N) ℂ) :
    (sigTop p i hi * tailForm p i hi L).trace.re = tailSum p i L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«re_trace_sigTop_tail» := P2M_GroundTheory_Heights__Heights_FourB_re_trace_sigTop_tail_2171dde6e7ba
