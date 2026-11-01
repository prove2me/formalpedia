-- Prove2me | Theorems.Thm_RobustSPUA_theorem_2_rank_probability
-- name    : RobustSPUA.theorem_2_rank_probability
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:44:12.346633+00:00
-- url     : https://prove2.me/theorems/50fc9dc0-3404-42c3-afce-38608867bce6
-- title:
--   Theorem 2, closing clause, p.5 — $\mathbf P(R_t\le k\mid r_t=s)=\sum_{i=s}^{k\wedge(n-t+s)}\binom{i-1}{s-1}\binom{n-i}{t-s}/\binom nt$
-- statement:
--   Let $n\ge1$ candidates arrive in a uniformly random order, let $R_t$ be the absolute rank and $r_t$ the partial rank of the $t$-th candidate. For all $t\in[n]$, $s\in[t]$ and $k\in[n]$, the probability that the $t$-th candidate is ranked in the top $k$ given that her partial rank is $s$ is
--   $$
--   \mathbf P(R_t\le k\mid r_t=s)=\sum_{i=s}^{k\wedge(n-t+s)}\frac{\binom{i-1}{s-1}\binom{n-i}{t-s}}{\binom nt}.
--   $$
--
--   These are the coefficients of the linear program $(LP)_{n,p}$ of Theorem 2; the identity says that the LP, written with explicit binomial coefficients, measures the probabilities of the process.
--
--   **Formalization Note** The left side is the count ratio $\#\{\pi: r_t=s,\ R_t\le k\}/\#\{\pi: r_t=s\}$ over all permutations of $[n]$ (`condRankProb`); the right side is `rankCoef`, with `Nat.choose`.
--
--   Differences from the source:
--   - encoding: P(R_t ≤ k | r_t = s) → the count ratio #{π : r_t = s, R_t ≤ k} / #{π : r_t = s} over all permutations of [n]; reason: the elementary conditional probability under the uniform permutation; the denominator n!/t is positive
--   - encoding: the closed form Σ_{i=s}^{k∧(n−t+s)} C(i−1,s−1)C(n−i,t−s)/C(n,t) → Nat.choose with natural-number subtraction, the sum cast to ℝ and divided by C(n,t); reason: every subtraction is in range for t ∈ [n], s ∈ [t], s ≤ i ≤ k∧(n−t+s)
--   - encoding: times t ∈ [n] and ranks R_t ∈ [n], 1-based → process times are 0-based (Fin n), the candidate at time t has rank π(t)+1; policies, POL, the LP and the coefficients keep the paper's 1-based (t, s); reason: Lean indexing convention; same instances
--   - encoding: the number of candidates n, implicitly positive (the min over k ∈ [n] in (1) and the initial state (1,1) need it) → the explicit hypothesis 1 ≤ n; reason: a nondegeneracy condition that only excludes the undefined case n = 0
-- source:
--   Perez-Salazar, Singh, Toriello, Robust Online Selection with Uncertain Offer Acceptance, arXiv:2112.00842v2, Theorem 2, p.5 (the clause 'where P(R_t ≤ k | r_t = s) = … is the probability the t-th candidate is ranked in the top k given that her partial rank is s')

import Mathlib
import Definitions.Def_RobustSPUA_Model
import Definitions.Def_RobustSPUA_LP

open Finset

namespace RobustSPUA

/-- S. Perez-Salazar, M. Singh, A. Toriello, *Robust Online Selection with Uncertain Offer Acceptance*, arXiv:2112.00842v2, Theorem 2, closing clause, p.5:
`P(R_t ≤ k | r_t = s) = ∑_{i=s}^{k∧(n−t+s)} C(i−1,s−1) C(n−i,t−s) / C(n,t)` for `t ∈ [n]`,
`s ∈ [t]`, `k ∈ [n]`, under the uniform arrival permutation.

**Formalization Note** The conditional probability is the count ratio `condRankProb` (the
denominator counts permutations with `r_t = s`, which is `n!/t > 0`); the closed form is
`rankCoef` with `Nat.choose`. -/
theorem theorem_2_rank_probability (n : ℕ) (hn : 1 ≤ n) :
    ∀ t ∈ Icc 1 n, ∀ s ∈ Icc 1 t, ∀ k ∈ Icc 1 n, condRankProb n t s k = rankCoef n t s k := by sorry

end RobustSPUA
