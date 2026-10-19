-- Prove2me | Theorems.Thm_PackingBounds_fullQuotient_radialToFull
-- name    : PackingBounds.fullQuotient_radialToFull
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:04.614989+00:00
-- url     : https://prove2.me/theorems/a1d524f4-4dc1-448e-bc1e-6899dfd7dbe8
-- title:
--   PackingBounds.fullQuotient_radialToFull
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
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap Topology
open PackingBounds

theorem PackingBounds.fullQuotient_radialToFull {d : ℕ}
    (f : CohnElkies.Admissible d) :
    fullQuotient (radialToFull f) = CohnElkies.quotient f := by sorry
