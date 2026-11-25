-- Prove2me | Theorems.Thm_SZ_digitSum_mul_pow
-- name    : SZ.digitSum_mul_pow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:40:44.843538+00:00
-- url     : https://prove2.me/theorems/c49a5e63-cd5b-45c2-ae56-4f3388e54b81
-- title:
--   SZ: digit Sum mul pow
-- statement:
--   Shifting a partial sum by `mˢ` produces an integer, explicitly.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/DigitParity.lean#L191-L202
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/DigitParity.lean#L191-L202

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
variable {m : ℕ} {d : ℕ → ℤ}

theorem SZ.digitSum_mul_pow (h : IsDigits m d) (s : ℕ) :
    digitSum m d s * (m : ℝ) ^ s
      = ((∑ i ∈ Finset.range s, d i * (m : ℤ) ^ (s - (i + 1)) : ℤ) : ℝ) := by sorry
