-- Prove2me | Theorems.Thm_RobustSPUA_proposition_5
-- name    : RobustSPUA.proposition_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:44:05.213573+00:00
-- url     : https://prove2.me/theorems/340ceb66-8fc8-428b-a2bb-ff7687d5125d
-- title:
--   Proposition 5, p.30 — every policy's occupation vector lies in $\mathrm{POL}$ (corrected: recursion for $t\ge2$)
-- statement:
--   Fix $n\ge1$ and $p\in(0,1]$. For every randomized Markov policy $\mathcal P$ of the SP-UA, let
--   $$
--   x_{t,s}=\mathbf P(\mathcal P\text{ reaches state }(t,s),\ \text{selects candidate}),\qquad
--   y_{t,s}=\mathbf P(\mathcal P\text{ reaches state }(t,s),\ \text{does not select candidate}).
--   $$
--   Then $(x,y)\in\mathrm{POL}$: $(x,y)\ge0$, $x_{1,1}+y_{1,1}=1$, and
--   $$
--   x_{t,s}+y_{t,s}=\frac1t\sum_{\sigma=1}^{t-1}\bigl(y_{t-1,\sigma}+(1-p)x_{t-1,\sigma}\bigr)\qquad\forall t\in\{2,\dots,n\},\ s\in[t].
--   $$
--
--   This is the "policies lie in the polytope" half of Theorem 1: the occupation probabilities of any policy satisfy the flow equations of the MDP.
--
--   **Formalization Note** POL is `POL n p` of the mission's LP definitions; the occupation probabilities are `occX`, `occY`, probabilities of events of the explicit outcome space.
--
--   Differences from the source:
--   - correction: POL with the recursion for all t ∈ [n], s ∈ [t] (p.30) → the recursion for t ∈ [2, n], as in Theorem 1 (p.5) and §4.2.1 (p.12); reason: at t = 1 the sum is empty and forces x_{1,1}+y_{1,1} = 0, contradicting x_{1,1}+y_{1,1} = 1; counterexample to the printed statement: n = 1, any p, the policy q(1,1) = 1 has x_{1,1} = 1, y_{1,1} = 0
--   - reading: γ*_n = sup_P γ_P over the policies of §3 (p.9), deterministic or randomized, Markovian (p.10) → all randomized Markov policies q, i.e. offer probabilities q(t,s) ∈ [0,1] at the states (t,s), t ∈ [n], s ∈ [t]; reason: the optimal policy of Theorem 2 is randomized, so the class must contain randomized policies; deterministic policies are the {0,1}-valued q; the paper restricts to Markovian policies (p.10)
--   - encoding: probabilities over the uniform arrival permutation and the accept/decline outcomes of offered candidates (p.9) → an explicit finite space Perm(Fin n) × Bool^n × Bool^n: uniform permutation, offer coins drawn with the policy's probability at the current state, i.i.d. Bernoulli(p) willingness coins; reason: the literal process written as a finite probability space; coins drawn after the process stops affect no event
--   - encoding: times t ∈ [n] and ranks R_t ∈ [n], 1-based → process times are 0-based (Fin n), the candidate at time t has rank π(t)+1; policies, POL, the LP and the coefficients keep the paper's 1-based (t, s); reason: Lean indexing convention; same instances
--   - encoding: 'reaches state (t,s)', 'selects / does not select candidate', 'collects a top k candidate' (pp.9, 10, 30) → reaching time t = no earlier offer was accepted; selecting = extending an offer; collecting a top-k candidate = reaching some time, offering, the candidate accepting, and its rank being ≤ k; reason: the paper's definitions written as events of the outcome space
--   - encoding: the number of candidates n, implicitly positive (the min over k ∈ [n] in (1) and the initial state (1,1) need it) → the explicit hypothesis 1 ≤ n; reason: a nondegeneracy condition that only excludes the undefined case n = 0
--   - encoding: vectors x, y and policies indexed by the states (t,s), t ∈ [n], s ∈ [t] → total real-valued functions of two natural numbers; reason: only the values at the states are constrained or read, so the instances are the same
-- source:
--   Perez-Salazar, Singh, Toriello, Robust Online Selection with Uncertain Offer Acceptance, arXiv:2112.00842v2, Proposition 5, p.30 (POL as defined on p.30, with the recursion range of Theorem 1, p.5)

import Mathlib
import Definitions.Def_RobustSPUA_Model
import Definitions.Def_RobustSPUA_LP

open Finset

namespace RobustSPUA

/-- S. Perez-Salazar, M. Singh, A. Toriello, *Robust Online Selection with Uncertain Offer Acceptance*, arXiv:2112.00842v2, Proposition 5, p.30 (corrected: recursion for `t ≥ 2`): for every policy, the
vector `x_{t,s} = P(reach (t,s), offer)`, `y_{t,s} = P(reach (t,s), pass)` lies in POL.

**Formalization Note** POL is the polytope of Theorem 1 (p.5), with the recursion for
`t ∈ [2, n]`; the p.30 restatement prints `∀ t ∈ [n]`, which makes POL empty (at `n = 1` the
policy `q ≡ 1` has `x_{1,1} + y_{1,1} = 1`, while the printed `t = 1` row forces `0`). -/
theorem proposition_5 (n : ℕ) (hn : 1 ≤ n) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (q : ℕ → ℕ → ℝ) (hq : IsPolicy n q) :
    POL n p (occX n p q) (occY n p q) := by sorry

end RobustSPUA
