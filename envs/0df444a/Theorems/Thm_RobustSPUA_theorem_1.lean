-- Prove2me | Theorems.Thm_RobustSPUA_theorem_1
-- name    : RobustSPUA.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:44:09.7696+00:00
-- url     : https://prove2.me/theorems/e7f4cd66-4fa7-4229-b363-4a7d84817bdb
-- title:
--   Theorem 1, p.5 — the policies of the SP-UA are exactly the points of $\mathrm{POL}$
-- statement:
--   Fix $n\ge1$ and $p\in(0,1]$, and let
--   $$
--   \mathrm{POL}=\Bigl\{(x,y)\ge0:\ x_{t,s}+y_{t,s}=\frac1t\sum_{\sigma=1}^{t-1}\bigl(y_{t-1,\sigma}+(1-p)x_{t-1,\sigma}\bigr)\ \forall t>1,\ s\in[t],\ \ x_{1,1}+y_{1,1}=1\Bigr\}.
--   $$
--
--   1. Any policy $\mathcal P$ for the SP-UA is represented as a vector in POL: its occupation probabilities $x_{t,s}=\mathbf P(\text{reach }(t,s),\text{ offer})$, $y_{t,s}=\mathbf P(\text{reach }(t,s),\text{ pass})$ satisfy $(x,y)\in\mathrm{POL}$.
--   2. Conversely, any $(x,y)\in\mathrm{POL}$ represents a policy: the policy that offers to the first candidate with probability $x_{1,1}$ and to the $t$-th candidate, when $r_t=s$, with probability $t\,x_{t,s}\big/\sum_{\sigma=1}^{t-1}(y_{t-1,\sigma}+(1-p)x_{t-1,\sigma})$ exists, and its occupation probabilities are $x$ and $y$.
--
--   Theorem 1 characterizes the space of all policies by a polytope that does not depend on the objective; it is the structural result behind the linear program of Theorem 2.
--
--   **Formalization Note** Part 2 is stated for every policy agreeing with the formula where the denominator is positive (`AgreesPOL`), together with the existence of one.
--
--   Differences from the source:
--   - reading: γ*_n = sup_P γ_P over the policies of §3 (p.9), deterministic or randomized, Markovian (p.10) → all randomized Markov policies q, i.e. offer probabilities q(t,s) ∈ [0,1] at the states (t,s), t ∈ [n], s ∈ [t]; reason: the optimal policy of Theorem 2 is randomized, so the class must contain randomized policies; deterministic policies are the {0,1}-valued q; the paper restricts to Markovian policies (p.10)
--   - reading: the policy that offers with probability t·x_{t,s}/(denominator), a formula undefined when the denominator is 0 → existence of a [0,1]-valued policy agreeing with the formula wherever the denominator is positive, and the conclusion for every such policy; reason: zero denominators occur (n = 2, p = 1, x_{1,1} = 1); such states are reached with probability 0, so every completion is covered
--   - encoding: probabilities over the uniform arrival permutation and the accept/decline outcomes of offered candidates (p.9) → an explicit finite space Perm(Fin n) × Bool^n × Bool^n: uniform permutation, offer coins drawn with the policy's probability at the current state, i.i.d. Bernoulli(p) willingness coins; reason: the literal process written as a finite probability space; coins drawn after the process stops affect no event
--   - encoding: times t ∈ [n] and ranks R_t ∈ [n], 1-based → process times are 0-based (Fin n), the candidate at time t has rank π(t)+1; policies, POL, the LP and the coefficients keep the paper's 1-based (t, s); reason: Lean indexing convention; same instances
--   - encoding: 'reaches state (t,s)', 'selects / does not select candidate', 'collects a top k candidate' (pp.9, 10, 30) → reaching time t = no earlier offer was accepted; selecting = extending an offer; collecting a top-k candidate = reaching some time, offering, the candidate accepting, and its rank being ≤ k; reason: the paper's definitions written as events of the outcome space
--   - reading: 'can be represented as a vector in POL', 'represents a policy' → (occX, occY) ∈ POL for every policy, and for (x, y) ∈ POL the formula policy has occupation vector (x, y); reason: the paragraph after the theorem on p.5 says x_{t,s}, y_{t,s} are the reach-and-offer and reach-and-pass probabilities
--   - encoding: the number of candidates n, implicitly positive (the min over k ∈ [n] in (1) and the initial state (1,1) need it) → the explicit hypothesis 1 ≤ n; reason: a nondegeneracy condition that only excludes the undefined case n = 0
--   - encoding: vectors x, y and policies indexed by the states (t,s), t ∈ [n], s ∈ [t] → total real-valued functions of two natural numbers; reason: only the values at the states are constrained or read, so the instances are the same
-- source:
--   Perez-Salazar, Singh, Toriello, Robust Online Selection with Uncertain Offer Acceptance, arXiv:2112.00842v2, Theorem 1, p.5

import Mathlib
import Definitions.Def_RobustSPUA_Model
import Definitions.Def_RobustSPUA_LP

open Finset

namespace RobustSPUA

/-- S. Perez-Salazar, M. Singh, A. Toriello, *Robust Online Selection with Uncertain Offer Acceptance*, arXiv:2112.00842v2, Theorem 1, p.5: any policy is represented as a vector of POL (its occupation
probabilities); conversely every `(x, y) ∈ POL` represents a policy, namely the policy that offers
to the first candidate with probability `x_{1,1}` and to the `t`-th candidate, of partial rank
`s`, with probability `t x_{t,s} / ∑_σ (y_{t−1,σ} + (1−p) x_{t−1,σ})`.

**Formalization Note** "Represented as a vector in POL" is `(occX, occY) ∈ POL`; "represents a
policy" is that the formula policy exists and every completion of it (where the denominator is
`0`) has occupation vector `(x, y)`. -/
theorem theorem_1 (n : ℕ) (hn : 1 ≤ n) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (∀ q : ℕ → ℕ → ℝ, IsPolicy n q → POL n p (occX n p q) (occY n p q)) ∧
    ∀ x y : ℕ → ℕ → ℝ, POL n p x y →
      (∃ q, IsPolicy n q ∧ AgreesPOL n p x y q) ∧
      ∀ q, IsPolicy n q → AgreesPOL n p x y q →
        ∀ t ∈ Icc 1 n, ∀ s ∈ Icc 1 t, occX n p q t s = x t s ∧ occY n p q t s = y t s := by sorry

end RobustSPUA
