-- Prove2me | Theorems.Thm_TauCeti_exists_sum_Icc_le_mul_of_isBigO
-- name    : TauCeti.exists_sum_Icc_le_mul_of_isBigO
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:46:19.834976+00:00
-- url     : https://prove2.me/theorems/72d799ee-f0b9-4678-acb2-df8eb3798b02
-- title:
--   A uniform linear bound from linear growth
-- statement:
--   Let $f:\mathbb N\to\mathbb R$ and assume $\sum_{1\le n\le\lfloor x\rfloor}f(n)=O(x)$ as $x\to\infty$. There is a real constant $C$ such that
--
--   $$
--   \sum_{n=1}^{N}f(n)\le CN\qquad\text{for every }N\in\mathbb N.
--   $$
--
--   This replaces an eventual growth bound by one valid at every natural cutoff, including zero.
--
--   Source and proof credit: the Tau Ceti contributors, [original declaration and proof](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Analysis/Asymptotics/SumWindow.lean#L108-L136), Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`; adapted to Lean 4.33.1.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Analysis/Asymptotics/SumWindow.lean#L108-L136

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

theorem TauCeti.exists_sum_Icc_le_mul_of_isBigO {f : ℕ → ℝ}
    (h : (fun x : ℝ ↦ ∑ n ∈ _root_.Finset.Icc 1 ⌊x⌋₊, f n) =O[_root_.Filter.atTop] fun x ↦ x) :
    ∃ C : ℝ, ∀ N : ℕ, ∑ n ∈ _root_.Finset.Icc 1 N, f n ≤ C * N := by sorry
