-- Prove2me | Theorems.Thm_RobustSPUA_proposition_7
-- name    : RobustSPUA.proposition_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:44:03.597383+00:00
-- url     : https://prove2.me/theorems/cd027403-798c-4591-94a9-76869b3a7468
-- title:
--   Proposition 7, p.32 — $\mathbf P(\mathcal P\text{ collects a top }k\text{ candidate})=\sum_{t,s}p\,x_{t,s}\mathbf P(R_t\le k\mid r_t=s)$
-- statement:
--   Fix $n\ge1$ and $p\in(0,1]$. Let $\mathcal P$ be any policy for the SP-UA and $(x,y)\in\mathrm{POL}$ its occupation vector, $x_{t,s}=\mathbf P(\mathcal P\text{ reaches }(t,s),\text{ selects candidate})$. Then for every $k\in[n]$,
--   $$
--   \mathbf P(\mathcal P\text{ collects a top }k\text{ candidate})=\sum_{t=1}^n\sum_{s=1}^t p\,x_{t,s}\,\mathbf P(R_t\le k\mid r_t=s).
--   $$
--
--   So the numerators of the robust ratio are linear in the occupation vector, which turns the max–min problem $\gamma^*_n$ into a linear program over POL.
--
--   **Formalization Note** $\mathbf P(R_t\le k\mid r_t=s)$ is the conditional probability under the uniform permutation (`condRankProb`), not its closed form.
--
--   Differences from the source:
--   - reading: γ*_n = sup_P γ_P over the policies of §3 (p.9), deterministic or randomized, Markovian (p.10) → all randomized Markov policies q, i.e. offer probabilities q(t,s) ∈ [0,1] at the states (t,s), t ∈ [n], s ∈ [t]; reason: the optimal policy of Theorem 2 is randomized, so the class must contain randomized policies; deterministic policies are the {0,1}-valued q; the paper restricts to Markovian policies (p.10)
--   - encoding: P(R_t ≤ k | r_t = s) → the count ratio #{π : r_t = s, R_t ≤ k} / #{π : r_t = s} over all permutations of [n]; reason: the elementary conditional probability under the uniform permutation; the denominator n!/t is positive
--   - encoding: probabilities over the uniform arrival permutation and the accept/decline outcomes of offered candidates (p.9) → an explicit finite space Perm(Fin n) × Bool^n × Bool^n: uniform permutation, offer coins drawn with the policy's probability at the current state, i.i.d. Bernoulli(p) willingness coins; reason: the literal process written as a finite probability space; coins drawn after the process stops affect no event
--   - encoding: times t ∈ [n] and ranks R_t ∈ [n], 1-based → process times are 0-based (Fin n), the candidate at time t has rank π(t)+1; policies, POL, the LP and the coefficients keep the paper's 1-based (t, s); reason: Lean indexing convention; same instances
--   - encoding: 'reaches state (t,s)', 'selects / does not select candidate', 'collects a top k candidate' (pp.9, 10, 30) → reaching time t = no earlier offer was accepted; selecting = extending an offer; collecting a top-k candidate = reaching some time, offering, the candidate accepting, and its rank being ≤ k; reason: the paper's definitions written as events of the outcome space
--   - encoding: the number of candidates n, implicitly positive (the min over k ∈ [n] in (1) and the initial state (1,1) need it) → the explicit hypothesis 1 ≤ n; reason: a nondegeneracy condition that only excludes the undefined case n = 0
--   - encoding: vectors x, y and policies indexed by the states (t,s), t ∈ [n], s ∈ [t] → total real-valued functions of two natural numbers; reason: only the values at the states are constrained or read, so the instances are the same
-- source:
--   Perez-Salazar, Singh, Toriello, Robust Online Selection with Uncertain Offer Acceptance, arXiv:2112.00842v2, Proposition 7, p.32

import Mathlib
import Definitions.Def_RobustSPUA_Model
import Definitions.Def_RobustSPUA_LP

open Finset

namespace RobustSPUA

/-- S. Perez-Salazar, M. Singh, A. Toriello, *Robust Online Selection with Uncertain Offer Acceptance*, arXiv:2112.00842v2, Proposition 7, p.32: for every policy with occupation vector `x` and every
`k ∈ [n]`, `P(P collects a top k candidate) = ∑_{t=1}^n ∑_{s=1}^t p x_{t,s} P(R_t ≤ k | r_t = s)`.

**Formalization Note** `P(R_t ≤ k | r_t = s)` is the count ratio `condRankProb` under the uniform
permutation (not the closed form). -/
theorem proposition_7 (n : ℕ) (hn : 1 ≤ n) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (q : ℕ → ℕ → ℝ) (hq : IsPolicy n q) :
    ∀ k ∈ Icc 1 n, prob n p q (collectsTop k) =
      ∑ t ∈ Icc 1 n, ∑ s ∈ Icc 1 t, p * occX n p q t s * condRankProb n t s k := by sorry

end RobustSPUA
