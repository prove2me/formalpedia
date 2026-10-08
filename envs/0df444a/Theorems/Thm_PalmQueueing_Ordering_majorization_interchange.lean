-- Prove2me | Theorems.Thm_PalmQueueing_Ordering_majorization_interchange
-- name    : PalmQueueing.Ordering.majorization_interchange
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T02:04:06.074987+00:00
-- url     : https://prove2.me/theorems/0d3bf9db-a1a1-4455-b064-22effb14c855
-- title:
--   Lemma 4.1.1 — one transposition of a reordering increases majorization
-- statement:
--   **Lemma 4.1.1**, the first of "two technical lemmas on majorization". Let
--   $x_1 \le \dots \le x_n$ and $y_1 \le \dots \le y_n$ be real numbers. Let $\gamma$ be a permutation
--   on $\{1,\dots,n\}$ such that there exist some $i,j$, $1 \le i < j \le n$, with
--   $\gamma(i) > \gamma(j)$, and let $\gamma'$ be obtained from $\gamma$ by interchanging its values on
--   $i$ and $j$. Then
--   $$ (y_{\gamma'} - x) \prec (y_\gamma - x) . \tag{4.1.16} $$
--
--   Undoing one inversion of $\gamma$ makes the difference vector **less spread out** in the
--   majorization order. Iterating drives $\gamma$ to the identity — which is Lemma 4.1.2, and which is
--   what makes FIFO, the discipline whose permutation is the identity, the extremal one.
--
--   The proof is a convexity argument. Since $y_{\gamma(i)} - y_{\gamma(j)} \ge 0$ and
--   $x_i - x_j \le 0$ there is $0 \le \epsilon \le 1$ with
--   $\epsilon(y_{\gamma(i)} - y_{\gamma(j)}) + (1-\epsilon)(x_i - x_j) = 0$, and the two coordinates in
--   which $y_{\gamma'} - x$ differs from $y_\gamma - x$ are then convex combinations of the
--   corresponding two. So $y_{\gamma'} - x$ lies in the convex hull of the permutations of
--   $y_\gamma - x$, which is majorization by Property 4.1.1.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 266, Lemma 4.1.1

import Mathlib
import Definitions.Def_PalmQueueing_Ordering_PartialOrders

/-!
# Lemma 4.1.1: one transposition of a reordering increases majorization (§4.1.3, p.266)
-/

namespace PalmQueueing.Ordering

/-- **Lemma 4.1.1** (p.266), the first of "two technical lemmas on majorization".

Let `x₁ ≤ x₂ ≤ … ≤ xₙ` and `y₁ ≤ y₂ ≤ … ≤ yₙ` be real numbers. Let `γ` be a permutation on
`{1, 2, …, n}` such that there exist some `i, j`, `1 ≤ i < j ≤ n`, with `γ(i) > γ(j)`, and let
`γ'` be the permutation obtained from `γ` by interchanging the values of `γ` on `i` and `j`:
`γ'(i) = γ(j)`, `γ'(j) = γ(i)`, and `γ'(k) = γ(k)` for `k ≠ i`, `k ≠ j`. Then

`(4.1.16)  (y_{γ'} − x) ≺ (y_γ − x)`.

Undoing one inversion of `γ` makes the difference vector `y_γ − x` **less spread out** in the
majorization order. Iterating drives `γ` to the identity, which is what Lemma 4.1.2 records and
what makes FIFO — the discipline whose permutation is the identity — the extremal one.

The proof is a convexity argument: since `y_{γ(i)} − y_{γ(j)} ≥ 0` and `x_i − x_j ≤ 0`, there is
`0 ≤ ε ≤ 1` with `ε(y_{γ(i)} − y_{γ(j)}) + (1 − ε)(x_i − x_j) = 0`, and the two coordinates of
`y_{γ'} − x` that differ from `y_γ − x` are then convex combinations of the corresponding two of
`y_γ − x`. So `y_{γ'} − x` lies in the convex hull of the permutations of `y_γ − x`, which is
majorization. -/
theorem majorization_interchange {n : ℕ} (x y : Fin n → ℝ)
    (hx : Monotone x) (hy : Monotone y)
    (g : Equiv.Perm (Fin n)) (i j : Fin n) (hij : i < j) (hgij : g j < g i)
    (g' : Equiv.Perm (Fin n))
    (hg'i : g' i = g j) (hg'j : g' j = g i)
    (hg'k : ∀ k : Fin n, k ≠ i → k ≠ j → g' k = g k) :
    Majorized (fun k => y (g' k) - x k) (fun k => y (g k) - x k) := by sorry

end PalmQueueing.Ordering
