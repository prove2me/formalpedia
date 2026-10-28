-- Prove2me | Theorems.Thm_QMCTriFree_Circuit_lemma_22
-- name    : QMCTriFree.Circuit.lemma_22
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:28:38.515726+00:00
-- url     : https://prove2.me/theorems/35bc2e23-3645-4193-af37-f62bb931e967
-- title:
--   Lemma 22 — if $\sum_{k\in S}x_k\le\eta\le1$ then $\prod_{k\in S}\sqrt{1-\beta^2x_k^2}\ge\sqrt{1-\beta^2\eta^2}$
-- statement:
--   Let $\{x_k:k\in S\}$ be nonnegative real numbers indexed by a finite set $S$, and $\eta\in[0,1]$. If $\sum_{k\in S}x_k\le\eta$, then for every $\beta\in[0,1]$,
--   $$\prod_{k\in S}\sqrt{1-\beta^2x_k^2}\ \ge\ \sqrt{1-\beta^2\eta^2}.$$
--
--   The product is smallest when all mass sits on one index. Combined with Lemma 7 it gives Corollary 8.
--
--   **Formalization Note** The paper says "positive"; its use in Corollary 8 includes zeros, so the statement is for nonnegative $x_k$, a harmless generalisation.
-- source:
--   King, An Improved Approximation Algorithm for Quantum Max-Cut on Triangle-Free Graphs, arXiv:2209.02589v3, p. 27, Lemma 22

import Mathlib

set_option autoImplicit false

namespace QMCTriFree.Circuit

/-- King, arXiv:2209.02589v3, p. 27, Lemma 22 (stated for nonnegative `x_k`): if
`∑_{k∈S} x_k ≤ η ∈ [0, 1]` then `∏_{k∈S} √(1 − β² x_k²) ≥ √(1 − β² η²)` for `β ∈ [0, 1]`. -/
theorem lemma_22 {ι : Type} (S : Finset ι) (x : ι → ℝ) (hx : ∀ k ∈ S, 0 ≤ x k)
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hsum : ∑ k ∈ S, x k ≤ η)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    Real.sqrt (1 - β ^ 2 * η ^ 2) ≤ ∏ k ∈ S, Real.sqrt (1 - β ^ 2 * x k ^ 2) := by sorry

end QMCTriFree.Circuit
