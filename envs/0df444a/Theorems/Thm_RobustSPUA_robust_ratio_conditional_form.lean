-- Prove2me | Theorems.Thm_RobustSPUA_robust_ratio_conditional_form
-- name    : RobustSPUA.robust_ratio_conditional_form
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:43:14.485345+00:00
-- url     : https://prove2.me/theorems/f6ca5a74-e623-4d20-8add-dc2bdc95e029
-- title:
--   §3, display, p.10 — $\gamma^*_n=\max_{\mathcal P}\min_k\mathbf P(\text{collect rank}\le k)/(1-(1-p)^k)=\max_{\mathcal P}\min_k\mathbf P(\text{collect top }k\mid\text{a top }k\text{ accepts})$
-- statement:
--   Fix $n\ge1$ and $p\in(0,1]$.
--
--   1. For every policy $\mathcal P$ and every $k\in[n]$, the probability that at least one of the top $k$ candidates accepts an offer is $1-(1-p)^k$.
--   2. The best robust ratio $\gamma^*_n=\sup_{\mathcal P}\gamma_{\mathcal P}$ satisfies
--   $$
--   \gamma^*_n=\max_{\mathcal P}\min_{k\in[n]}\frac{\mathbf P(\mathcal P\text{ collects a candidate with rank}\le k)}{1-(1-p)^k}
--   =\max_{\mathcal P}\min_{k\in[n]}\mathbf P(\mathcal P\text{ collects a top }k\text{ candidate}\mid\text{a top }k\text{ candidate accepts}),
--   $$
--   both maxima over policies being attained.
--
--   The display restates the objective: the robust ratio of a policy is its worst-case probability of collecting a top-$k$ candidate, conditioned on some top-$k$ candidate being willing to accept.
--
--   **Formalization Note** $\gamma^*_n$ is `IsLUB (robustRatios n p)`, and each max is `IsGreatest` over the policies' values; $\mathbf P(A\mid B)=\mathbf P(A\cap B)/\mathbf P(B)$.
--
--   Differences from the source:
--   - reading: γ*_n = sup_P γ_P over the policies of §3 (p.9), deterministic or randomized, Markovian (p.10) → all randomized Markov policies q, i.e. offer probabilities q(t,s) ∈ [0,1] at the states (t,s), t ∈ [n], s ∈ [t]; reason: the optimal policy of Theorem 2 is randomized, so the class must contain randomized policies; deterministic policies are the {0,1}-valued q; the paper restricts to Markovian policies (p.10)
--   - encoding: 'optimal value', 'max', γ*_n = sup → IsLUB for the supremum, IsGreatest for each attained optimum; reason: Lean order-theoretic convention; attainment is asserted exactly where the paper writes max or optimal
--   - encoding: P(A | B), a conditional probability → P(A ∩ B)/P(B); reason: elementary definition; P(B) = 1 − (1−p)^k > 0
--   - encoding: probabilities over the uniform arrival permutation and the accept/decline outcomes of offered candidates (p.9) → an explicit finite space Perm(Fin n) × Bool^n × Bool^n: uniform permutation, offer coins drawn with the policy's probability at the current state, i.i.d. Bernoulli(p) willingness coins; reason: the literal process written as a finite probability space; coins drawn after the process stops affect no event
--   - encoding: times t ∈ [n] and ranks R_t ∈ [n], 1-based → process times are 0-based (Fin n), the candidate at time t has rank π(t)+1; policies, POL, the LP and the coefficients keep the paper's 1-based (t, s); reason: Lean indexing convention; same instances
--   - encoding: 'reaches state (t,s)', 'selects / does not select candidate', 'collects a top k candidate' (pp.9, 10, 30) → reaching time t = no earlier offer was accepted; selecting = extending an offer; collecting a top-k candidate = reaching some time, offering, the candidate accepting, and its rank being ≤ k; reason: the paper's definitions written as events of the outcome space
--   - reading: the display replaces the denominator of (1) by 1 − (1−p)^k without comment → an explicit conjunct: P(at least one top k candidate accepts) = 1 − (1−p)^k for every policy and k ∈ [n]; reason: this identity is the content of that replacement, and it ties the first max of the display to the robust ratio (1)
--   - encoding: the number of candidates n, implicitly positive (the min over k ∈ [n] in (1) and the initial state (1,1) need it) → the explicit hypothesis 1 ≤ n; reason: a nondegeneracy condition that only excludes the undefined case n = 0
--   - encoding: vectors x, y and policies indexed by the states (t,s), t ∈ [n], s ∈ [t] → total real-valued functions of two natural numbers; reason: only the values at the states are constrained or read, so the instances are the same
-- source:
--   Perez-Salazar, Singh, Toriello, Robust Online Selection with Uncertain Offer Acceptance, arXiv:2112.00842v2, §3, display, p.10

import Mathlib
import Definitions.Def_RobustSPUA_Model

open Finset

namespace RobustSPUA

/-- S. Perez-Salazar, M. Singh, A. Toriello, *Robust Online Selection with Uncertain Offer Acceptance*, arXiv:2112.00842v2, §3, display, p.10:
`γ*_n = max_P min_{k ∈ [n]} P(P collects a candidate with rank ≤ k) / (1 − (1−p)^k)
      = max_P min_{k ∈ [n]} P(P collects a top k candidate | a top k candidate accepts)`.

For every policy and `k ∈ [n]`, `P(at least one top k candidate accepts) = 1 − (1−p)^k` (the
denominator of (1) used in the display); and both minima, maximized over policies, are attained
and equal `γ*_n = sup_P γ_P`.

**Formalization Note** `γ*_n` is the least upper bound of the robust ratios of all randomized
Markov policies; each "max" is `IsGreatest`. The conditional probability `P(A | B)` is
`P(A ∩ B)/P(B)`. -/
theorem robust_ratio_conditional_form (n : ℕ) (hn : 1 ≤ n) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (∀ q : ℕ → ℕ → ℝ, IsPolicy n q → ∀ k ∈ Icc 1 n, prob n p q (topAccepts k) = 1 - (1 - p) ^ k) ∧
    ∃ v : ℝ, IsLUB (robustRatios n p) v ∧
      IsGreatest {r | ∃ q, IsPolicy n q ∧
        r = ⨅ k : Fin n, prob n p q (collectsTop (k.val + 1)) / (1 - (1 - p) ^ (k.val + 1))} v ∧
      IsGreatest {r | ∃ q, IsPolicy n q ∧
        r = ⨅ k : Fin n, prob n p q (fun ω => collectsTop (k.val + 1) ω ∧ topAccepts (k.val + 1) ω) /
          prob n p q (topAccepts (k.val + 1))} v := by sorry

end RobustSPUA
