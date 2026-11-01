-- Prove2me | Theorems.Thm_RobustSPUA_partial_ranks_independent
-- name    : RobustSPUA.partial_ranks_independent
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:43:21.827032+00:00
-- url     : https://prove2.me/theorems/cac2bb54-a510-487b-9ef8-ebf8077fc916
-- title:
--   §3, display, p.9 — partial ranks are independent and $r_{t+1}$ is uniform on $[t+1]$
-- statement:
--   Let the $n\ge1$ candidates arrive in a uniformly random order and let $r_t$ be the partial rank of the $t$-th candidate. Then the partial ranks are independent: every vector $(s_1,\dots,s_n)$ with $s_t\in[t]$ is the vector of partial ranks of exactly one arrival order, so
--   $$
--   \mathbf P(r_1=s_1,\dots,r_n=s_n)=\frac1{n!}\qquad\text{for all } s_t\in[t].
--   $$
--   In particular, for $t<n$, $s\in[t]$ and $\sigma\in[t+1]$,
--   $$
--   \mathbf P(r_{t+1}=\sigma\mid r_t=s)=\mathbf P(r_{t+1}=\sigma)=\frac1{t+1}.
--   $$
--
--   This is the fact that makes the states $(t,r_t)$ a Markov chain with uniform transitions, on which the MDP formulation of the problem rests.
--
--   **Formalization Note** Probabilities under the uniform permutation are counts over the $n!$ permutations of `Fin n`. Times are 0-based, so the paper's pair of times $(t,t+1)$ is Lean's $(t,u)$ with `u = t + 1`, and the paper's $1/(t+1)$ is `1 / (t.val + 2)`.
--
--   Differences from the source:
--   - generalization: 'partial ranks at each stage are independent' and the pairwise display P(r_{t+1}=σ | r_t=s) = P(r_{t+1}=σ) = 1/(t+1) → the joint law: each admissible vector of partial ranks is realized by exactly one permutation (uniform on ∏_t [t]), together with the pairwise display; reason: the joint law is mutual independence with uniform marginals; it implies the sentence and the display
--   - encoding: times t ∈ [n] and ranks R_t ∈ [n], 1-based → process times are 0-based (Fin n), the candidate at time t has rank π(t)+1; policies, POL, the LP and the coefficients keep the paper's 1-based (t, s); reason: Lean indexing convention; same instances
--   - encoding: probabilities under the uniform permutation → counts of permutations, and count ratios; reason: the uniform law on n! permutations; same values
--   - encoding: the number of candidates n, implicitly positive (the min over k ∈ [n] in (1) and the initial state (1,1) need it) → the explicit hypothesis 1 ≤ n; reason: a nondegeneracy condition that only excludes the undefined case n = 0
-- source:
--   Perez-Salazar, Singh, Toriello, Robust Online Selection with Uncertain Offer Acceptance, arXiv:2112.00842v2, §3, display, p.9

import Mathlib
import Definitions.Def_RobustSPUA_Model

open Finset

namespace RobustSPUA

/-- S. Perez-Salazar, M. Singh, A. Toriello, *Robust Online Selection with Uncertain Offer Acceptance*, arXiv:2112.00842v2, §3, display, p.9: partial ranks are independent, and
`P(r_{t+1} = σ | r_t = s) = P(r_{t+1} = σ) = 1/(t+1)` for `t < n`, `s ∈ [t]`, `σ ∈ [t+1]`.

Under the uniform arrival permutation: (1) the joint law of the partial ranks is uniform on
`∏_t [t]` (every admissible vector of partial ranks is realized by exactly one permutation),
which is "partial ranks at each stage are independent"; (2) the display, as count ratios.

**Formalization Note** Times are 0-based: Lean's `t`, `u = t+1` are the paper's `t+1`, `t+2`, so
the paper's `1/(t+1)` is `1/(t.val+2)`. Probabilities under the uniform permutation are count
ratios over `Equiv.Perm (Fin n)` (`n!` permutations). -/
theorem partial_ranks_independent (n : ℕ) (hn : 1 ≤ n) :
    (∀ r : Fin n → ℕ, (∀ t : Fin n, 1 ≤ r t ∧ r t ≤ t.val + 1) →
      (univ.filter (fun π : Equiv.Perm (Fin n) => ∀ t, partialRank π t = r t)).card = 1) ∧
    (∀ t u : Fin n, u.val = t.val + 1 → ∀ s ∈ Icc 1 (t.val + 1), ∀ σ ∈ Icc 1 (u.val + 1),
      ((univ.filter (fun π : Equiv.Perm (Fin n) =>
          partialRank π t = s ∧ partialRank π u = σ)).card : ℝ) /
        ((univ.filter (fun π : Equiv.Perm (Fin n) => partialRank π t = s)).card : ℝ) =
          1 / ((t.val : ℝ) + 2) ∧
      ((univ.filter (fun π : Equiv.Perm (Fin n) => partialRank π u = σ)).card : ℝ) /
        (n.factorial : ℝ) = 1 / ((t.val : ℝ) + 2)) := by sorry

end RobustSPUA
