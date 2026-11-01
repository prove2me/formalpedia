-- Prove2me | Theorems.Thm_RobustSPUA_theorem_2
-- name    : RobustSPUA.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:44:09.106163+00:00
-- url     : https://prove2.me/theorems/500666f7-9613-4d05-9d45-444da331ceff
-- title:
--   Theorem 2, p.5 — the best robust ratio $\gamma^*_n$ is the value of $(LP)_{n,p}$, and every optimal solution gives a $\gamma^*_n$-robust policy
-- statement:
--   Fix the number of candidates $n\ge1$ and the acceptance probability $p\in(0,1]$. Let $\gamma^*_n=\sup_{\mathcal P}\gamma_{\mathcal P}$ be the best robust ratio of the SP-UA, the supremum over all (randomized, Markov) policies. Consider the linear program
--   $$
--   (LP)_{n,p}\qquad \max_{x\ge0}\ \gamma\quad\text{s.t.}\quad x_{t,s}\le\frac1t\Bigl(1-p\sum_{\tau=1}^{t-1}\sum_{\sigma=1}^{\tau}x_{\tau,\sigma}\Bigr)\ \ \forall t\in[n],\ s\in[t],
--   $$
--   $$
--   \gamma\le\frac{p}{1-(1-p)^k}\sum_{t=1}^n\sum_{s=1}^t x_{t,s}\,\mathbf P(R_t\le k\mid r_t=s)\ \ \forall k\in[n],
--   \qquad
--   \mathbf P(R_t\le k\mid r_t=s)=\sum_{i=s}^{k\wedge(n-t+s)}\frac{\binom{i-1}{s-1}\binom{n-i}{t-s}}{\binom nt}.
--   $$
--   Then:
--
--   1. $(LP)_{n,p}$ attains its optimal value, and this value equals $\gamma^*_n$;
--   2. for every optimal solution $(x^*,\gamma^*_n)$ of $(LP)_{n,p}$, the randomized policy $\mathcal P^*$ that at state $(t,s)$ makes an offer with probability
--   $$
--   \frac{t\,x^*_{t,s}}{1-p\sum_{\tau=1}^{t-1}\sum_{\sigma=1}^{\tau}x^*_{\tau,\sigma}}
--   $$
--   exists and is $\gamma^*_n$-robust, i.e. $\gamma^*_n\le\gamma_{\mathcal P^*}$;
--   3. the closed form above is indeed the probability that the $t$-th candidate is ranked in the top $k$ given that her partial rank is $s$, for all $t\in[n]$, $s\in[t]$, $k\in[n]$.
--
--   Theorem 2 reduces the max–min problem over all policies to an explicit linear program of polynomial size, and gives the optimal policy in closed form from any optimal LP solution.
--
--   **Formalization Note** The supremum is `IsLUB (robustRatios n p) v` and the LP optimum is `IsGreatest` of the feasible values of $\gamma$; "$(x^*,\gamma^*_n)$ optimal" is `LPFeasible n p x v`. The LP coefficients are the closed form (`rankCoef`); the conditional probability is the count ratio `condRankProb` over permutations. Robust ratios are probabilities of events of the explicit process, not LP expressions.
--
--   Differences from the source:
--   - reading: γ*_n = sup_P γ_P over the policies of §3 (p.9), deterministic or randomized, Markovian (p.10) → all randomized Markov policies q, i.e. offer probabilities q(t,s) ∈ [0,1] at the states (t,s), t ∈ [n], s ∈ [t]; reason: the optimal policy of Theorem 2 is randomized, so the class must contain randomized policies; deterministic policies are the {0,1}-valued q; the paper restricts to Markovian policies (p.10)
--   - reading: the policy that offers with probability t·x_{t,s}/(denominator), a formula undefined when the denominator is 0 → existence of a [0,1]-valued policy agreeing with the formula wherever the denominator is positive, and the conclusion for every such policy; reason: zero denominators occur (n = 2, p = 1, x_{1,1} = 1); such states are reached with probability 0, so every completion is covered
--   - encoding: 'optimal value', 'max', γ*_n = sup → IsLUB for the supremum, IsGreatest for each attained optimum; reason: Lean order-theoretic convention; attainment is asserted exactly where the paper writes max or optimal
--   - encoding: the closed form Σ_{i=s}^{k∧(n−t+s)} C(i−1,s−1)C(n−i,t−s)/C(n,t) → Nat.choose with natural-number subtraction, the sum cast to ℝ and divided by C(n,t); reason: every subtraction is in range for t ∈ [n], s ∈ [t], s ≤ i ≤ k∧(n−t+s)
--   - encoding: P(R_t ≤ k | r_t = s) → the count ratio #{π : r_t = s, R_t ≤ k} / #{π : r_t = s} over all permutations of [n]; reason: the elementary conditional probability under the uniform permutation; the denominator n!/t is positive
--   - encoding: probabilities over the uniform arrival permutation and the accept/decline outcomes of offered candidates (p.9) → an explicit finite space Perm(Fin n) × Bool^n × Bool^n: uniform permutation, offer coins drawn with the policy's probability at the current state, i.i.d. Bernoulli(p) willingness coins; reason: the literal process written as a finite probability space; coins drawn after the process stops affect no event
--   - encoding: times t ∈ [n] and ranks R_t ∈ [n], 1-based → process times are 0-based (Fin n), the candidate at time t has rank π(t)+1; policies, POL, the LP and the coefficients keep the paper's 1-based (t, s); reason: Lean indexing convention; same instances
--   - encoding: 'reaches state (t,s)', 'selects / does not select candidate', 'collects a top k candidate' (pp.9, 10, 30) → reaching time t = no earlier offer was accepted; selecting = extending an offer; collecting a top-k candidate = reaching some time, offering, the candidate accepting, and its rank being ≤ k; reason: the paper's definitions written as events of the outcome space
--   - encoding: the number of candidates n, implicitly positive (the min over k ∈ [n] in (1) and the initial state (1,1) need it) → the explicit hypothesis 1 ≤ n; reason: a nondegeneracy condition that only excludes the undefined case n = 0
--   - encoding: vectors x, y and policies indexed by the states (t,s), t ∈ [n], s ∈ [t] → total real-valued functions of two natural numbers; reason: only the values at the states are constrained or read, so the instances are the same
-- source:
--   Perez-Salazar, Singh, Toriello, Robust Online Selection with Uncertain Offer Acceptance, arXiv:2112.00842v2, Theorem 2, p.5 (restated as Theorem 7, p.33)

import Mathlib
import Definitions.Def_RobustSPUA_Model
import Definitions.Def_RobustSPUA_LP

open Finset

namespace RobustSPUA

/-- S. Perez-Salazar, M. Singh, A. Toriello, *Robust Online Selection with Uncertain Offer Acceptance*, arXiv:2112.00842v2, Theorem 2, p.5 (restated as Theorem 7, p.33): the best robust ratio `γ*_n` equals
the optimal value of (LP)_{n,p}; for every optimal solution `(x*, γ*_n)` the randomized policy
`P*` that at state `(t, s)` offers with probability `t x*_{t,s} / (1 − p ∑_{τ<t} ∑_σ x*_{τ,σ})` is
`γ*_n`-robust; and `∑_{i=s}^{k∧(n−t+s)} C(i−1,s−1) C(n−i,t−s)/C(n,t)` is `P(R_t ≤ k | r_t = s)`.

**Formalization Note**
* `γ*_n = sup_P γ_P` over randomized Markov policies is `IsLUB (robustRatios n p) v`; "the
  optimal value of (LP)_{n,p}" is `IsGreatest` of the feasible `γ`'s (the LP optimum is attained).
* `(x, v)` with `LPFeasible n p x v` is exactly an optimal solution. Where
  `1 − p ∑_{τ<t} ∑_σ x_{τ,σ} = 0` the formula is undefined; the policy exists (a `[0,1]`-valued
  completion) and every completion is `γ*_n`-robust (`v ≤ γ_q`).
* `n ≥ 1`, `0 < p ≤ 1` are the paper's standing assumptions (p.3). -/
theorem theorem_2 (n : ℕ) (hn : 1 ≤ n) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (∃ v : ℝ,
      IsLUB (robustRatios n p) v ∧
      IsGreatest {γ : ℝ | ∃ x, LPFeasible n p x γ} v ∧
      ∀ x : ℕ → ℕ → ℝ, LPFeasible n p x v →
        (∃ q, IsPolicy n q ∧ AgreesLP n p x q) ∧
        ∀ q, IsPolicy n q → AgreesLP n p x q → v ≤ robustRatio n p q) ∧
    (∀ t ∈ Icc 1 n, ∀ s ∈ Icc 1 t, ∀ k ∈ Icc 1 n, condRankProb n t s k = rankCoef n t s k) := by sorry

end RobustSPUA
