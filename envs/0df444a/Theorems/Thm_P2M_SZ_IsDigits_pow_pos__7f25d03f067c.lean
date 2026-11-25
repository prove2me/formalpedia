-- Prove2me | Theorems.Thm_P2M_SZ_IsDigits_pow_pos__7f25d03f067c
-- name    : P2M_SZ_IsDigits_pow_pos__7f25d03f067c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:38:53.845385+00:00
-- url     : https://prove2.me/theorems/1ab82ddb-b9dc-407d-ac08-cdc9b7eea5e3
-- title:
--   P2 M SZ Is Digits pow pos  7f25d03f067c: P2 M SZ Is Digits pow pos  7f25d03f067c
-- statement:
--   The P2 M SZ Is Digits pow pos  7f25d03f067c construction uses the P2 M SZ Is Digits pow pos  7f25d03f067c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/DigitParity.lean#L86-L86
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/DigitParity.lean#L86-L86

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_DigitParity
set_option autoImplicit false
open SZ
open Finset Filter Topology
open SZ.IsDigits
variable {m : ℕ} {d : ℕ → ℤ}

theorem P2M_SZ_IsDigits_pow_pos__7f25d03f067c (h : IsDigits m d) (k : ℕ) : (0 : ℝ) < (m : ℝ) ^ k := by sorry

alias «SZ».«IsDigits».«pow_pos'» := P2M_SZ_IsDigits_pow_pos__7f25d03f067c
