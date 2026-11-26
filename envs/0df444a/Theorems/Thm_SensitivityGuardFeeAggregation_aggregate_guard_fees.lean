-- Prove2me | Theorems.Thm_SensitivityGuardFeeAggregation_aggregate_guard_fees
-- name    : SensitivityGuardFeeAggregation.aggregate_guard_fees
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T15:48:48.376102+00:00
-- url     : https://prove2.me/theorems/7273615d-0599-4d2a-aa39-33d003b7d6aa
-- title:
--   Exact socket accounting for occupied and cold guards
-- statement:
--   Let $O\subseteq\mathcal Q$ be the occupied checks, and let each check have $d_Q$ physical sockets, with $\sum_{\mathcal Q}d_Q=D$. Suppose a cold check costs at most $d_Q z$, while an occupied check costs at most $w_Q+(d_Q-1)u_Q$. Then
--   $$
--   \sum_{Q\in\mathcal Q}\mathrm{fee}(Q)
--   \le\left(D-\sum_{Q\in O}d_Q\right)z
--   +\sum_{Q\in O}\bigl(w_Q+(d_Q-1)u_Q\bigr).
--   $$
--   The subtraction in the first coefficient is exact natural-number subtraction: it counts the sockets in the complementary checks.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/GuardFeeAggregation.lean lines 11–40; SHA256 88bac109cbbb2a380117cfea2c961ecfb94b61eac62120a4562b22e692fb2117; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityGuardFeeAggregation
end SensitivityGuardFeeAggregation


/-! Exact aggregation of occupied and unoccupied physical guard costs. -/
open SensitivityGuardFeeAggregation
open scoped Classical BigOperators
set_option autoImplicit false

theorem SensitivityGuardFeeAggregation.aggregate_guard_fees {G : Type} (checks occupied : Finset G)
    (hsub : occupied ⊆ checks) (slots : G → ℕ) (D : ℕ)
    (hslots : ∑ check ∈ checks, slots check = D)
    (fee combined upward : G → ℝ) (baseline : ℝ)
    (hcold : ∀ check ∈ checks, check ∉ occupied → fee check ≤ slots check * baseline)
    (hhot : ∀ check ∈ occupied,
      fee check ≤ combined check + (slots check - 1 : ℕ) * upward check) :
    (∑ check ∈ checks, fee check) ≤
      ((D - ∑ check ∈ occupied, slots check : ℕ) : ℝ) * baseline +
        ∑ check ∈ occupied, (combined check + (slots check - 1 : ℕ) * upward check) := by sorry
