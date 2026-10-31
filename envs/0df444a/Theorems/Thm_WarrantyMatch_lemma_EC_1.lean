-- Prove2me | Theorems.Thm_WarrantyMatch_lemma_EC_1
-- name    : WarrantyMatch.lemma_EC_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:37:29.485707+00:00
-- url     : https://prove2.me/theorems/8c52af57-8548-4048-8f58-d00ee8bf4cd0
-- title:
--   Lemma EC.1 — $E f(X-Y)\le\frac{(1+\epsilon)^2}{4}f(m-1)$ under KS distance $\le\epsilon$ (corrected: tightness for $\epsilon\le 1$)
-- statement:
--   Let $m\ge 1$ and let $f:\mathbb R\to\mathbb R$ be convex and nondecreasing with $f(x)=0$ for $x\le 0$. Let $X$ and $Y$ be independent random variables on $\{1,\dots,m\}$ with laws $p=(p_1,\dots,p_m)$ and $\tilde p=(\tilde p_1,\dots,\tilde p_m)$, at Kolmogorov–Smirnov distance at most $\varepsilon$:
--   $$
--   \Bigl|\sum_{i=1}^k p_i-\sum_{i=1}^k\tilde p_i\Bigr|\le\varepsilon,\qquad k=1,\dots,m .
--   $$
--   Then
--   $$
--   E[f(X-Y)]=\sum_{j=1}^m\sum_{i=1}^m\tilde p_i\,p_j\,f(j-i)\le\frac{(1+\varepsilon)^2}{4}\,f(m-1).
--   $$
--   Moreover, for every $0\le\varepsilon\le 1$ the bound is attained: some pair of probability vectors $(p,\tilde p)$ satisfying the constraints achieves equality.
--
--   This is the extremal inequality behind the distribution-free bound of Proposition 1: conditionally on the inventory time, the dates of the customer and of the reassigned device are two laws at bounded KS distance, and the lemma bounds the expected mismatch cost by a two-point worst case.
--
--   **Formalization Note** The lemma is stated on probability vectors $p,\tilde p:\mathbb N\to\mathbb R$ of which only the entries $1,\dots,m$ matter (nonnegative there, summing to $1$), and $E[f(X-Y)]$ is the double sum of (EC.1). The printed proof's splitting step (p.ec3) can violate the KS constraint; the statement is not affected.
--
--   Differences from the source:
--   - reading: X and Y not stated to be independent → the objective is the double sum Σ_j Σ_i p̃_i p_j f(j − i) of (EC.1), i.e. X and Y independent; reason: without independence the lemma is false (m = 2, ε = 0, f = x⁺, X uniform on {1,2}, Y = 3 − X gives E f(X − Y) = 1/2 > 1/4), and the proof's (EC.1) uses the product law
--   - encoding: discrete random variables X, Y with laws p, p̃ on [1, m] → probability vectors p, q : ℕ → ℝ, nonnegative on {1, …, m} and summing to 1 there; reason: the law determines E f(X − Y) for independent X, Y; same instances
--   - reading: positive convex increasing f with f(x) = 0 for x ≤ 0 → f convex on ℝ, monotone (nondecreasing), f(x) = 0 for x ≤ 0; reason: "positive" and strictly increasing contradict f = 0 on (−∞, 0]; nonnegativity follows from the other conditions, and the proof of Proposition 1 states the hypothesis as "convex non-decreasing"
--   - correction: "Furthermore, this bound is tight" (for every ε) → the bound is attained for 0 ≤ ε ≤ 1; reason: for ε > 1 the bound exceeds f(m − 1) ≥ E f(X − Y); counterexample m = 2, f = x⁺, ε = 2: the bound is 9/4 but E f(X − Y) ≤ 1
-- source:
--   Calmon–Graves–Lemmens, Warranty Matching in a Consumer Electronics Closed-Loop Supply Chain, INSEAD WP 2020/03/TOM (SSRN 3357683), Lemma EC.1, p.ec2; objective (EC.1), p.ec3; extremal pair after (EC.2), p.ec4

import Mathlib

open Finset

namespace WarrantyMatch

/-- **Lemma EC.1** (KS-constrained extremal bound). Let `m ≥ 1`, and let `f : ℝ → ℝ` be convex
and nondecreasing with `f x = 0` for `x ≤ 0`. Let `p` (the law of `X`) and `p̃` (the law of
`Y`) be probability vectors on `{1, …, m}` whose cumulative sums differ by at most `ε`:
`|∑_{i ≤ k} p_i − ∑_{i ≤ k} p̃_i| ≤ ε` for `k = 1, …, m`. Then
1. `E[f(X − Y)] = ∑_{j=1}^m ∑_{i=1}^m p̃_i p_j f(j − i) ≤ (1 + ε)²/4 · f(m − 1)`;
2. for `0 ≤ ε ≤ 1` the bound is attained by some feasible pair `(p, p̃)`.
Calmon–Graves–Lemmens, *Warranty Matching in a Consumer Electronics Closed-Loop Supply Chain*,
INSEAD WP 2020/03/TOM (SSRN 3357683), Lemma EC.1, p.ec2; objective and constraints as in (EC.1), p.ec3; extremal pair p.ec4.

**Formalization Note** `X` and `Y` are independent (the objective of (EC.1) is the double
sum); the lemma is stated on the probability vectors `p, q : ℕ → ℝ` (`q` is `p̃`), of which
only the entries `1, …, m` matter. "Positive … increasing" is read as nonnegative (implied) and
nondecreasing (`Monotone`). Tightness is claimed only for `ε ≤ 1`: for `ε > 1` the bound
exceeds `f(m − 1) ≥ E f(X − Y)` (corrected). -/
theorem lemma_EC_1 (m : ℕ) (hm : 1 ≤ m) (f : ℝ → ℝ) (hconv : ConvexOn ℝ Set.univ f)
    (hmono : Monotone f) (hf0 : ∀ x ≤ 0, f x = 0) :
    (∀ (ε : ℝ) (p q : ℕ → ℝ), (∀ i ∈ Icc 1 m, 0 ≤ p i) → (∀ i ∈ Icc 1 m, 0 ≤ q i) →
        ∑ i ∈ Icc 1 m, p i = 1 → ∑ i ∈ Icc 1 m, q i = 1 →
        (∀ k ∈ Icc 1 m, |∑ i ∈ Icc 1 k, p i - ∑ i ∈ Icc 1 k, q i| ≤ ε) →
        ∑ j ∈ Icc 1 m, ∑ i ∈ Icc 1 m, q i * p j * f ((j : ℝ) - i) ≤
          (1 + ε) ^ 2 / 4 * f ((m : ℝ) - 1)) ∧
    (∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∃ p q : ℕ → ℝ,
        (∀ i ∈ Icc 1 m, 0 ≤ p i) ∧ (∀ i ∈ Icc 1 m, 0 ≤ q i) ∧
        ∑ i ∈ Icc 1 m, p i = 1 ∧ ∑ i ∈ Icc 1 m, q i = 1 ∧
        (∀ k ∈ Icc 1 m, |∑ i ∈ Icc 1 k, p i - ∑ i ∈ Icc 1 k, q i| ≤ ε) ∧
        ∑ j ∈ Icc 1 m, ∑ i ∈ Icc 1 m, q i * p j * f ((j : ℝ) - i) =
          (1 + ε) ^ 2 / 4 * f ((m : ℝ) - 1)) := by sorry

end WarrantyMatch
