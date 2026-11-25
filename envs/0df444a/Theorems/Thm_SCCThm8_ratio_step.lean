-- Prove2me | Theorems.Thm_SCCThm8_ratio_step
-- name    : SCCThm8.ratio_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:44:27.692425+00:00
-- url     : https://prove2.me/theorems/70095acd-5635-567f-bb84-6cf86e6c4553
-- title:
--   SCCThm8: ratio step
-- statement:
--   Monotonicity of `C(3k,⌊3k/2⌋) · 27^k / (8^k · trin k)`, in cross-multiplied form.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Numeric.lean#L162-L204
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Numeric.lean#L162-L204

module
public import Mathlib
public import Definitions.Def_SCCThm8_Numeric
set_option autoImplicit true
@[expose] public section
public section
open SCCThm8

theorem SCCThm8.ratio_step (k : ℕ) : 8 * trin (k + 1) * cen k ≤ 27 * cen (k + 1) * trin k := by sorry
