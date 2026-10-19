-- Prove2me | Theorems.Thm_PackingBounds_fullLinearProgram_eq_radial
-- name    : PackingBounds.fullLinearProgram_eq_radial
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:05.603159+00:00
-- url     : https://prove2.me/theorems/7e3a3d5f-1f3c-4175-b46f-98a6367b8b9d
-- title:
--   PackingBounds.fullLinearProgram_eq_radial
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
open Filter
open scoped FourierTransform SchwartzMap Topology
open PackingBounds

theorem PackingBounds.fullLinearProgram_eq_radial (d : ℕ) :
    fullLinearProgram d = CohnElkies.linearProgram d := by sorry
