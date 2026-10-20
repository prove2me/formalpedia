-- Prove2me | Theorems.Thm_SpherePacking_Alternative_fourierReal_schwartzDilation_apply
-- name    : SpherePacking.Alternative.fourierReal_schwartzDilation_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:05.603159+00:00
-- url     : https://prove2.me/theorems/df2044e1-1c31-4952-abaf-356f90019e2e
-- title:
--   SpherePacking.Alternative.fourierReal_schwartzDilation_apply
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
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory
open scoped FourierTransform Real Topology
open SpherePacking SpherePacking.Alternative

theorem SpherePacking.Alternative.fourierReal_schwartzDilation_apply {d : ℕ} (a : ℝ) (ha : 0 < a)
    (f : Schwartz d) (ξ : Ambient d) :
    fourierReal (schwartzDilation a ha.ne' f) ξ =
      (a ^ d)⁻¹ * fourierReal f (a⁻¹ • ξ) := by sorry
