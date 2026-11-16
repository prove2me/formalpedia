-- Prove2me | Theorems.Thm_PlanarDFVS_SingleExp_Supplement_corollary_3_4
-- name    : PlanarDFVS.SingleExp.Supplement.corollary_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:32:47.557198+00:00
-- url     : https://prove2.me/theorems/3cc948e3-ee3e-4c9f-9489-252bab79eca5
-- title:
--   Corollary 3.4 — a weighted random vertex lies in a small DFVS with probability > 1/6
-- statement:
--   Let $D$ be a loopless plane digraph (parallel arcs allowed) with vertex set $V(D)$ and a fixed embedding. For a vertex $v$ let $b(v)$ be half the number of alternating corners at $v$, let $w(v)=b(v)-1$ be its weight, and let $L=\sum_{v\in V(D)}w(v)$. Let $k\in\mathbb N$ and let $X$ be a directed feedback vertex set of $D$ with $|X|\le k$. If $L>3k$, then
--
--   $$\frac{w(X)}{L}=\frac{\sum_{v\in X}w(v)}{L}>\frac16 .$$
--
--   When every weight is nonnegative, $w(X)/L$ is the probability $\Pr[v^*\in X]$ that a vertex $v^*$ sampled with probability $w(v)/L$ for each $v$ lies in $X$; this is the sampling step of the $6.75^k$ algorithm (Theorem 4.1), applied to a fixed target solution $X$.
--
--   **Formalization Note** Weights are integers, compared and divided in the reals; $L>3k$ is an integer comparison, so $L>0$ and the division is genuine.
--
--   Differences from the source:
--   - encoding: plane digraph with corners → Fin n vertices, Fin m arcs, a geometric drawing with ray-ordered rotations (the published base definitions); reason: same instances as the published Lemma 3.3
--   - generalization: probability Pr[v∗ ∈ X] under sampling with probabilities w(v)/L → the ratio w(X)/L, with no nonnegativity hypothesis on the weights; reason: the source's proof computes Pr[v∗ ∈ X] = w(X)/L, so wherever the sampling law exists the two coincide; the Lean clause also covers instances with negative weights
--   - generalization: the §3.1 setting (weakly connected, at least one arc) → every loopless plane digraph; reason: specializes to the source's setting; with no arcs every weight is −1, so L > 3k fails, and disconnected digraphs are covered by the published Lemma 3.3
-- source:
--   Daniel Lokshtanov, Saket Saurabh, Jie Xue, STOC 2027 submission #1569 (October 2026), p. 6 (PDF p. 6), Corollary 3.4

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Graphs

open scoped BigOperators
open Classical

namespace PlanarDFVS.SingleExp.Supplement

open PlanarDFVS.SingleExp

theorem corollary_3_4 (n m : ℕ) (G : Graph n m) (E : Drawing G) (hl : Loopless G)
    (k : ℕ) (X : Finset (Fin n)) (hX : IsDFVS G X) (hk : X.card ≤ k)
    (hL : (3 * k : ℤ) < totalWeight E) :
    (1 / 6 : ℝ) < (∑ v ∈ X, (weight E v : ℝ)) / (totalWeight E : ℝ) := by sorry

end PlanarDFVS.SingleExp.Supplement
