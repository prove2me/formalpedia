-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_KernelPositive_line_apply_0ab5ddcbd25d
-- name    : P2M_GroundTheory_Heights__Heights_Regular_KernelPositive_line_apply_0ab5ddcbd25d
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:17:35.494155+00:00
-- url     : https://prove2.me/theorems/ed13d258-fe53-4021-8ba3-dd8abd387b4b
-- title:
--   P2 M Ground Theory Heights  Heights Regular Kernel Positive line apply 0ab5ddcbd25d: P2 M Ground Theory Heights  Heights Regular Kernel Positive line apply 0ab5ddcbd25d
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Kernel Positive line apply 0ab5ddcbd25d construction uses the P2 M Ground Theory Heights  Heights Regular Kernel Positive line apply 0ab5ddcbd25d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PKernelPositive.lean#L89-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PKernelPositive.lean#L89-L90

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PKernelPositive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.KernelPositive

theorem P2M_GroundTheory_Heights__Heights_Regular_KernelPositive_line_apply_0ab5ddcbd25d {n : ℕ} (z : Fin n → ℂ) (t : ℂ) (k : Fin n) : line z t k = z k + t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«KernelPositive».«line_apply» := P2M_GroundTheory_Heights__Heights_Regular_KernelPositive_line_apply_0ab5ddcbd25d
