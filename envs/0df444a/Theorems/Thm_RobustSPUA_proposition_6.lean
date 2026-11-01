-- Prove2me | Theorems.Thm_RobustSPUA_proposition_6
-- name    : RobustSPUA.proposition_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:44:06.608505+00:00
-- url     : https://prove2.me/theorems/ea492749-cc6d-45b8-aaa5-5905f5fa4378
-- title:
--   Proposition 6, p.31 — every point of $\mathrm{POL}$ is the occupation vector of an explicit policy
-- statement:
--   Fix $n\ge1$ and $p\in(0,1]$, and let $(x,y)\in\mathrm{POL}$. Consider the randomized policy $\mathcal P$ that, in state $(t,s)$, makes an offer to the $t$-th candidate with probability $x_{1,1}$ if $t=1$ and
--   $$
--   \frac{t\,x_{t,s}}{\sum_{\sigma=1}^{t-1}\bigl(y_{t-1,\sigma}+(1-p)x_{t-1,\sigma}\bigr)}\qquad\text{if }t>1.
--   $$
--   Then:
--
--   1. $\mathcal P$ is a policy: these numbers lie in $[0,1]$ wherever the denominator is positive, so a policy with these offer probabilities exists;
--   2. every such policy (whatever it does at states where the denominator vanishes) satisfies
--   $$
--   x_{t,s}=\mathbf P(\mathcal P\text{ reaches state }(t,s),\ \text{selects candidate}),\qquad y_{t,s}=\mathbf P(\mathcal P\text{ reaches state }(t,s),\ \text{does not select candidate})
--   $$
--   for all $t\in[n]$ and $s\in[t]$.
--
--   This is the converse half of Theorem 1: POL is exactly the set of occupation vectors of policies.
--
--   **Formalization Note** "Agrees with $(x,y)$" (`AgreesPOL`) fixes the offer probability only where the denominator is positive; at the other states, which are reached with probability $0$, the policy is arbitrary.
--
--   Differences from the source:
--   - reading: POL as restated on p.30, with the recursion for all t ∈ [n] (an empty set) → POL of Theorem 1 (p.5), with the recursion for t ∈ [2, n]; reason: with the printed range POL is empty and the statement vacuous; the main text (pp.5, 12) gives t > 1
--   - reading: the policy that offers with probability t·x_{t,s}/(denominator), a formula undefined when the denominator is 0 → existence of a [0,1]-valued policy agreeing with the formula wherever the denominator is positive, and the conclusion for every such policy; reason: zero denominators occur (n = 2, p = 1, x_{1,1} = 1); such states are reached with probability 0, so every completion is covered
--   - encoding: probabilities over the uniform arrival permutation and the accept/decline outcomes of offered candidates (p.9) → an explicit finite space Perm(Fin n) × Bool^n × Bool^n: uniform permutation, offer coins drawn with the policy's probability at the current state, i.i.d. Bernoulli(p) willingness coins; reason: the literal process written as a finite probability space; coins drawn after the process stops affect no event
--   - encoding: times t ∈ [n] and ranks R_t ∈ [n], 1-based → process times are 0-based (Fin n), the candidate at time t has rank π(t)+1; policies, POL, the LP and the coefficients keep the paper's 1-based (t, s); reason: Lean indexing convention; same instances
--   - encoding: 'reaches state (t,s)', 'selects / does not select candidate', 'collects a top k candidate' (pp.9, 10, 30) → reaching time t = no earlier offer was accepted; selecting = extending an offer; collecting a top-k candidate = reaching some time, offering, the candidate accepting, and its rank being ≤ k; reason: the paper's definitions written as events of the outcome space
--   - encoding: the number of candidates n, implicitly positive (the min over k ∈ [n] in (1) and the initial state (1,1) need it) → the explicit hypothesis 1 ≤ n; reason: a nondegeneracy condition that only excludes the undefined case n = 0
--   - encoding: vectors x, y and policies indexed by the states (t,s), t ∈ [n], s ∈ [t] → total real-valued functions of two natural numbers; reason: only the values at the states are constrained or read, so the instances are the same
-- source:
--   Perez-Salazar, Singh, Toriello, Robust Online Selection with Uncertain Offer Acceptance, arXiv:2112.00842v2, Proposition 6, p.31

import Mathlib
import Definitions.Def_RobustSPUA_Model
import Definitions.Def_RobustSPUA_LP

open Finset

namespace RobustSPUA

/-- S. Perez-Salazar, M. Singh, A. Toriello, *Robust Online Selection with Uncertain Offer Acceptance*, arXiv:2112.00842v2, Proposition 6, p.31: for `(x, y) ∈ POL`, the randomized policy that offers with
probability `x_{1,1}` at `t = 1` and `t x_{t,s} / ∑_σ (y_{t−1,σ} + (1−p) x_{t−1,σ})` at `t > 1` is a
policy, and its occupation probabilities are `x` and `y`.

**Formalization Note** POL has its recursion for `t ∈ [2, n]` (as on p.5). Where the
denominator is `0` the formula is undefined; the first conjunct asserts that a policy agreeing
with the formula wherever the denominator is positive exists, and the second that **every** such
policy has occupation vector `(x, y)`. -/
theorem proposition_6 (n : ℕ) (hn : 1 ≤ n) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (x y : ℕ → ℕ → ℝ) (hxy : POL n p x y) :
    (∃ q, IsPolicy n q ∧ AgreesPOL n p x y q) ∧
    ∀ q, IsPolicy n q → AgreesPOL n p x y q →
      ∀ t ∈ Icc 1 n, ∀ s ∈ Icc 1 t, occX n p q t s = x t s ∧ occY n p q t s = y t s := by sorry

end RobustSPUA
