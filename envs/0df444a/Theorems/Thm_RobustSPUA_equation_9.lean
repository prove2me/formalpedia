-- Prove2me | Theorems.Thm_RobustSPUA_equation_9
-- name    : RobustSPUA.equation_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:44:17.013609+00:00
-- url     : https://prove2.me/theorems/636b1bc0-d4ca-46f4-8414-70e0498f43b8
-- title:
--   (9), p.13 — $\gamma^*_n$ as a maximum over policies, over $\mathrm{POL}$, and as a linearized program
-- statement:
--   Fix $n\ge1$ and $p\in(0,1]$. The best robust ratio is attained and satisfies
--   $$
--   \gamma^*_n=\max_{\mathcal P}\min_{k\in[n]}\frac{\mathbf P(\mathcal P\text{ collects a top }k\text{ candidate})}{1-(1-p)^k}
--   =\max_{(x,y)\in\mathrm{POL}}\min_{k\in[n]}\frac{p\sum_{t=1}^n\sum_{s=1}^t x_{t,s}\mathbf P(R_t\le k\mid r_t=s)}{1-(1-p)^k}
--   $$
--   $$
--   =\max\Bigl\{\gamma:\ (x,y)\in\mathrm{POL},\ \gamma\le\frac{p\sum_{t=1}^n\sum_{s=1}^t x_{t,s}\mathbf P(R_t\le k\mid r_t=s)}{1-(1-p)^k}\ \ \forall k\in[n]\Bigr\}.
--   $$
--
--   Equation (9) is the passage from policies to a finite-dimensional optimization problem: the best robust ratio is the value of a linear program over the policy polytope.
--
--   **Formalization Note** Each "max" is `IsGreatest` with the same value $v$. The set of robust ratios (1) of all policies, whose denominator is the probability that some top $k$ candidate accepts, also has greatest element $v$, so $v=\gamma^*_n$ is attained; the first max as printed, with denominator $1-(1-p)^k$, is stated separately. $\mathbf P(R_t\le k\mid r_t=s)$ is `condRankProb`.
--
--   Differences from the source:
--   - reading: γ*_n = sup_P γ_P over the policies of §3 (p.9), deterministic or randomized, Markovian (p.10) → all randomized Markov policies q, i.e. offer probabilities q(t,s) ∈ [0,1] at the states (t,s), t ∈ [n], s ∈ [t]; reason: the optimal policy of Theorem 2 is randomized, so the class must contain randomized policies; deterministic policies are the {0,1}-valued q; the paper restricts to Markovian policies (p.10)
--   - encoding: 'optimal value', 'max', γ*_n = sup → IsLUB for the supremum, IsGreatest for each attained optimum; reason: Lean order-theoretic convention; attainment is asserted exactly where the paper writes max or optimal
--   - encoding: P(R_t ≤ k | r_t = s) → the count ratio #{π : r_t = s, R_t ≤ k} / #{π : r_t = s} over all permutations of [n]; reason: the elementary conditional probability under the uniform permutation; the denominator n!/t is positive
--   - encoding: probabilities over the uniform arrival permutation and the accept/decline outcomes of offered candidates (p.9) → an explicit finite space Perm(Fin n) × Bool^n × Bool^n: uniform permutation, offer coins drawn with the policy's probability at the current state, i.i.d. Bernoulli(p) willingness coins; reason: the literal process written as a finite probability space; coins drawn after the process stops affect no event
--   - encoding: times t ∈ [n] and ranks R_t ∈ [n], 1-based → process times are 0-based (Fin n), the candidate at time t has rank π(t)+1; policies, POL, the LP and the coefficients keep the paper's 1-based (t, s); reason: Lean indexing convention; same instances
--   - encoding: 'reaches state (t,s)', 'selects / does not select candidate', 'collects a top k candidate' (pp.9, 10, 30) → reaching time t = no earlier offer was accepted; selecting = extending an offer; collecting a top-k candidate = reaching some time, offering, the candidate accepting, and its rank being ≤ k; reason: the paper's definitions written as events of the outcome space
--   - reading: (9) writes γ*_n, with the first max having denominator 1 − (1−p)^k → the robust ratios (1), with denominator P(at least one top k candidate accepts), have greatest element v, and the first max as printed has the same value v; reason: (1) and the first max of (9) differ only by that denominator, equal by the display of p.10, and both are asserted
--   - encoding: the number of candidates n, implicitly positive (the min over k ∈ [n] in (1) and the initial state (1,1) need it) → the explicit hypothesis 1 ≤ n; reason: a nondegeneracy condition that only excludes the undefined case n = 0
--   - encoding: vectors x, y and policies indexed by the states (t,s), t ∈ [n], s ∈ [t] → total real-valued functions of two natural numbers; reason: only the values at the states are constrained or read, so the instances are the same
-- source:
--   Perez-Salazar, Singh, Toriello, Robust Online Selection with Uncertain Offer Acceptance, arXiv:2112.00842v2, (9), p.13

import Mathlib
import Definitions.Def_RobustSPUA_Model
import Definitions.Def_RobustSPUA_LP

open Finset

namespace RobustSPUA

/-- S. Perez-Salazar, M. Singh, A. Toriello, *Robust Online Selection with Uncertain Offer Acceptance*, arXiv:2112.00842v2, (9), p.13: `γ*_n` is attained over policies, and equals
`max_{(x,y) ∈ POL} min_{k ∈ [n]} p ∑_{t,s} x_{t,s} P(R_t ≤ k | r_t = s) / (1 − (1−p)^k)`, which equals
`max {γ : (x,y) ∈ POL, γ ≤ p ∑_{t,s} x_{t,s} P(R_t ≤ k | r_t = s) / (1 − (1−p)^k) ∀ k ∈ [n]}`.

**Formalization Note** Each "max" is `IsGreatest` (the maximum exists and equals the common
value `v`). The first `IsGreatest` is over the robust ratios (1), whose denominator is
`P(at least one top k candidate accepts)`; the second is the first max as printed in (9), with
denominator `1 − (1−p)^k`. POL has its recursion for `t ∈ [2, n]` (as on p.5).
`P(R_t ≤ k | r_t = s)` is the count ratio `condRankProb`. -/
theorem equation_9 (n : ℕ) (hn : 1 ≤ n) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∃ v : ℝ, IsGreatest (robustRatios n p) v ∧
      IsGreatest {r | ∃ q, IsPolicy n q ∧
        r = ⨅ k : Fin n, prob n p q (collectsTop (k.val + 1)) / (1 - (1 - p) ^ (k.val + 1))} v ∧
      IsGreatest {r | ∃ x y, POL n p x y ∧ r = polValue n p x} v ∧
      IsGreatest {γ | ∃ x y, POL n p x y ∧ ∀ k ∈ Icc 1 n,
        γ ≤ p * (∑ t ∈ Icc 1 n, ∑ s ∈ Icc 1 t, x t s * condRankProb n t s k) /
          (1 - (1 - p) ^ k)} v := by sorry

end RobustSPUA
