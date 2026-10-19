-- Prove2me | Theorems.Thm_PackingBounds_PackingBridge_volume_half_ball
-- name    : PackingBounds.PackingBridge.volume_half_ball
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:04.614989+00:00
-- url     : https://prove2.me/theorems/b232b9ba-e775-4461-b133-095d4305367b
-- title:
--   PackingBounds.PackingBridge.volume_half_ball
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | SpherePacking | external Lean 4.33.1 validation; bundle SHA256 ecca43e9570778e44777003bd5984d4ec94cd395fce5324c69b88ac50ad79ed2

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric
open scoped ENNReal FourierTransform SchwartzMap Topology
open PackingBounds PackingBounds.PackingBridge

theorem PackingBounds.PackingBridge.volume_half_ball {d : ℕ} (hd : 0 < d) :
    volume (ball (0 : CohnElkies.Euclidean d) (1 / 2 : ℝ)) =
      ENNReal.ofReal (CohnElkies.unitBallVolume d / (2 : ℝ) ^ d) := by sorry
