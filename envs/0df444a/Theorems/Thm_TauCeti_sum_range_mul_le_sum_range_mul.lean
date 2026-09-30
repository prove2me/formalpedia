-- Prove2me | Theorems.Thm_TauCeti_sum_range_mul_le_sum_range_mul
-- name    : TauCeti.sum_range_mul_le_sum_range_mul
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:46:23.759986+00:00
-- url     : https://prove2.me/theorems/fd71b20f-b3d9-4a00-b68c-9ba91685ec31
-- title:
--   Abel's inequality, comparison form
-- statement:
--   Let $R$ be a preordered ring whose order is preserved by addition and by left multiplication by nonnegative elements. Let $f,g,w:\mathbb N\to R$ and $N\in\mathbb N$. Assume $\sum_{i<k}f(i)\le\sum_{i<k}g(i)$ for every $k\le N$, $w(i+1)\le w(i)$ whenever $i+1<N$, and $w(N-1)\ge0$, where natural subtraction is truncated at zero. Then
--
--   $$
--   \sum_{i<N}w(i)f(i)\le\sum_{i<N}w(i)g(i).
--   $$
--
--   This comparison transfers bounds on partial sums to sums weighted by a decreasing nonnegative sequence.
--
--   Source and proof credit: the Tau Ceti contributors, [original declaration and proof](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Algebra/Order/BigOperators/Sum/ByParts.lean#L39-L64), Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`; adapted to Lean 4.33.1.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Algebra/Order/BigOperators/Sum/ByParts.lean#L39-L64

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Defs

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Comparing weighted sums through their partial sums

If every initial partial sum of `f` is at most the corresponding partial sum of `g`, then the
same comparison holds after weighting both sequences by a nonnegative, antitone weight `w`:
`∑_{i < N} w i * f i ≤ ∑_{i < N} w i * g i`. This is Abel's inequality in its comparison form.
Summation by parts (`Finset.sum_range_by_parts`) writes the difference of the two weighted sums
as the last weight times the last partial-sum difference plus the successive decrements of `w`
times the earlier partial-sum differences, and every one of these products is nonnegative.

No sign condition on `f` or `g` is needed. The typical use takes `g` constant: a bound
`∑_{i < k} f i ≤ k • C` on all partial sums then gives `∑ w i * f i ≤ (∑ w i) * C` for every
nonnegative antitone weight.

## Main results

* `TauCeti.sum_range_mul_le_sum_range_mul`: the weighted comparison.
-/

 section

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

open Finset

variable {R : Type*} [Ring R] [Preorder R] [IsOrderedAddMonoid R] [PosMulMono R]

theorem TauCeti.sum_range_mul_le_sum_range_mul {f g w : ℕ → R} {N : ℕ}
    (hfg : ∀ k ≤ N, ∑ i ∈ _root_.Finset.range k, f i ≤ ∑ i ∈ _root_.Finset.range k, g i)
    (hw : ∀ i, i + 1 < N → w (i + 1) ≤ w i) (hw0 : 0 ≤ w (N - 1)) :
    ∑ i ∈ _root_.Finset.range N, w i * f i ≤ ∑ i ∈ _root_.Finset.range N, w i * g i := by sorry
