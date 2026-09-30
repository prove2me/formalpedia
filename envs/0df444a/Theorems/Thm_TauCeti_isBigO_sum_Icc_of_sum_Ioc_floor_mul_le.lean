-- Prove2me | Theorems.Thm_TauCeti_isBigO_sum_Icc_of_sum_Ioc_floor_mul_le
-- name    : TauCeti.isBigO_sum_Icc_of_sum_Ioc_floor_mul_le
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:46:24.09717+00:00
-- url     : https://prove2.me/theorems/2aac68f2-349d-474d-9616-7c5d491eaa45
-- title:
--   Summing windows
-- statement:
--   Let $f:\mathbb N\to\mathbb R$ be nonnegative, and let $q,K\in\mathbb R$ with $0\le q<1$. Suppose that, for all sufficiently large real $x$, $\sum_{\lfloor qx\rfloor<n\le\lfloor x\rfloor}f(n)\le Kx$. Then
--
--   $$
--   \sum_{1\le n\le\lfloor x\rfloor}f(n)=O(x)\qquad(x\to\infty).
--   $$
--
--   Bounds on fixed-ratio windows therefore control the entire summatory function.
--
--   Source and proof credit: the Tau Ceti contributors, [original declaration and proof](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Analysis/Asymptotics/SumWindow.lean#L42-L106), Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`; adapted to Lean 4.33.1.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Analysis/Asymptotics/SumWindow.lean#L42-L106

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Tactic.FieldSimp

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Linear growth of partial sums from a window bound

If nonnegative terms `f n` have sums over the multiplicative windows `q x < n ≤ x` bounded by a
multiple of `x`, for a fixed ratio `0 ≤ q < 1` and all large `x`, then their partial sums
`∑_{1 ≤ n ≤ x} f n` are `O(x)`: the partial sum up to `x` is the window sum plus the partial sum
up to `q x`, and the window bounds form a geometric series.

This is the summation step of Chebyshev-type bounds, where a local estimate on windows
`(q x, x]` comes from a smoothed average and the global linear bound is what is needed.

## Main results

* `TauCeti.isBigO_sum_Icc_of_sum_Ioc_floor_mul_le`: a window bound `O(x)` implies partial sums
  `O(x)`.
* `TauCeti.exists_sum_Icc_le_mul_of_isBigO`: partial sums that are `O(x)` are bounded by `C N`
  at every natural cutoff `N`, with one constant `C`.
-/

 section

open Asymptotics Filter

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

theorem TauCeti.isBigO_sum_Icc_of_sum_Ioc_floor_mul_le {f : ℕ → ℝ} (hf : 0 ≤ f) {q K : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (h : ∀ᶠ x : ℝ in _root_.Filter.atTop, ∑ n ∈ _root_.Finset.Ioc ⌊q * x⌋₊ ⌊x⌋₊, f n ≤ K * x) :
    (fun x : ℝ ↦ ∑ n ∈ _root_.Finset.Icc 1 ⌊x⌋₊, f n) =O[_root_.Filter.atTop] fun x ↦ x := by sorry
