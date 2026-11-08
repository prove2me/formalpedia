-- Prove2me | Theorems.Thm_VolunteerNotify_claim_1
-- name    : VolunteerNotify.claim_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T05:36:56.738937+00:00
-- url     : https://prove2.me/theorems/4c2d850a-9285-4bae-b9d4-7e6fde1d2e1b
-- title:
--   Claim 1 — the value of (30) is at most $(1-c/n)^n$
-- statement:
--   Fix $n\ge1$ volunteers, a task type and a time, and let $c\in[0,1]$. Let $x_v,p_v\in[0,1]$ with $c=\sum_{v=1}^n x_vp_v$, that is, $x$ is feasible for program (30), which maximizes $\prod_v(1-x_vp_v)$. Then
--   $$
--   \prod_{v=1}^n(1-x_vp_v)\le\Bigl(1-\frac cn\Bigr)^n.
--   $$
--   This bounds the probability that nobody responds, given the expected number of responses.
--
--   Differences from the source:
--   - encoding: the value of the maximization (30) is at most (1 − c/n)ⁿ → the bound at every feasible point; reason: a bound on a maximum is a bound at every feasible point
--   - encoding: x_{v,s,t}, p_{v,s} of the fixed pair (s, t), with V = n → `x p : Fin n → ℝ` with values in [0, 1]; reason: (s, t) is fixed; the range comes from (1) and §3; volunteers are `Fin n`
--   - encoding: a fixed number of volunteers V = n → `n : ℕ` with `1 ≤ n`; reason: ℕ is {1, 2, …} in the source
-- source:
--   Manshadi, Rodilitz, Online Policies for Efficient Volunteer Crowdsourcing, arXiv:2002.08474v7, Claim 1 and program (30), p.36

import Mathlib

namespace VolunteerNotify

/-- Claim 1, Manshadi–Rodilitz, arXiv:2002.08474v7, p.36: for `n` volunteers the value of program
(30), maximize `∏_v (1 − x_v p_v)` subject to `c = ∑_v x_v p_v`, with `c ∈ [0, 1]`, is at most
`(1 − c/n)ⁿ`.

**Formalization Note.** The bound on the value is stated at every feasible point. `x_v, p_v ∈ [0, 1]`
come from (1) and §3; `(s, t)` is fixed and dropped from the notation. -/
theorem claim_1 (n : ℕ) (hn : 1 ≤ n) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) (x p : Fin n → ℝ)
    (hx : ∀ v, x v ∈ Set.Icc (0 : ℝ) 1) (hp : ∀ v, p v ∈ Set.Icc (0 : ℝ) 1)
    (hsum : c = ∑ v, x v * p v) : ∏ v, (1 - x v * p v) ≤ (1 - c / n) ^ n := by sorry

end VolunteerNotify
