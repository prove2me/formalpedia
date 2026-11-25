-- Prove2me | Theorems.Thm_SZ_digitReal_lt_digitSum_add
-- name    : SZ.digitReal_lt_digitSum_add
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:40:38.399492+00:00
-- url     : https://prove2.me/theorems/747e52c8-3db6-49a8-8cca-e098d1db6793
-- title:
--   SZ: digit Real lt digit Sum add
-- statement:
--   **Strict tail bound.**  If some digit at an index `≥ k` is at most `m - 2`, the tail
--   beyond `k` is strictly less than `m^{-k}` — by a definite margin.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/DigitParity.lean#L158-L186
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/DigitParity.lean#L158-L186

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

theorem SZ.digitReal_lt_digitSum_add (h : IsDigits m d) {k i₀ : ℕ} (hk : k ≤ i₀)
    (hsmall : d i₀ ≤ (m : ℤ) - 2) :
    digitReal m d < digitSum m d k + 1 / (m : ℝ) ^ k := by sorry
