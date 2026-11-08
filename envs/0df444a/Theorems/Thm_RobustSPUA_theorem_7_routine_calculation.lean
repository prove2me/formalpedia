-- Prove2me | Theorems.Thm_RobustSPUA_theorem_7_routine_calculation
-- name    : RobustSPUA.theorem_7_routine_calculation
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T12:44:21.130703+00:00
-- url     : https://prove2.me/theorems/7f4562d3-8b01-4bb1-aa7f-b28a8dde1264
-- title:
--   Proof of Theorem 7, p.33 — on $\mathrm{POL}$, $1-p\sum_{\tau<t}\sum_{\sigma\le\tau}x_{\tau,\sigma}=\sum_{\sigma<t}(y_{t-1,\sigma}+(1-p)x_{t-1,\sigma})$
-- statement:
--   Fix $n\ge1$ and $p\in(0,1]$, and let $(x,y)\in\mathrm{POL}$. Then for every $t\in\{2,\dots,n\}$,
--   $$
--   1-p\sum_{\tau=1}^{t-1}\sum_{\sigma=1}^{\tau}x_{\tau,\sigma}=\sum_{\sigma=1}^{t-1}\bigl(y_{t-1,\sigma}+(1-p)x_{t-1,\sigma}\bigr).
--   $$
--
--   This identity turns the denominator of the policy of Proposition 6 into the denominator of the policy of Theorem 2, so that the optimal solutions of $(LP)_{n,p}$ yield optimal policies.
--
--   **Formalization Note** The left side is `slackLP p x t`, the right side `polD p x y t`.
--
--   Differences from the source:
--   - generalization: the identity for the POL point (x*, y*) of an optimal solution of (LP)_{n,p} → the identity for every (x, y) ∈ POL; reason: the calculation uses only membership in POL; the optimal point is a special case
--   - reading: the identity with t unrestricted → t ∈ [2, n]; reason: at t = 1 the left side is 1 and the right side an empty sum; Proposition 6 uses the identity only for t > 1
--   - reading: POL as restated on p.30, with the recursion for all t ∈ [n] (an empty set) → POL of Theorem 1 (p.5), with the recursion for t ∈ [2, n]; reason: with the printed range POL is empty and the statement vacuous; the main text (pp.5, 12) gives t > 1
--   - encoding: the number of candidates n, implicitly positive (the min over k ∈ [n] in (1) and the initial state (1,1) need it) → the explicit hypothesis 1 ≤ n; reason: a nondegeneracy condition that only excludes the undefined case n = 0
--   - encoding: vectors x, y and policies indexed by the states (t,s), t ∈ [n], s ∈ [t] → total real-valued functions of two natural numbers; reason: only the values at the states are constrained or read, so the instances are the same
-- source:
--   Perez-Salazar, Singh, Toriello, Robust Online Selection with Uncertain Offer Acceptance, arXiv:2112.00842v2, proof of Theorem 7, p.33 ('A routine calculation shows that …')

import Mathlib
import Definitions.Def_RobustSPUA_Model
import Definitions.Def_RobustSPUA_LP

open Finset

namespace RobustSPUA

/-- S. Perez-Salazar, M. Singh, A. Toriello, *Robust Online Selection with Uncertain Offer Acceptance*, arXiv:2112.00842v2, proof of Theorem 7, p.33: on POL,
`1 − p ∑_{τ<t} ∑_{σ=1}^τ x_{τ,σ} = ∑_{σ=1}^{t−1} (y_{t−1,σ} + (1−p) x_{t−1,σ})` for `t ∈ [2, n]`.

**Formalization Note** At `t = 1` the left side is `1` and the right side an empty sum, so the
identity is for `t ≥ 2`, the range on which Proposition 6 uses it. It is stated for every point
of POL (the page applies it to the point of an optimal solution). -/
theorem theorem_7_routine_calculation (n : ℕ) (hn : 1 ≤ n) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (x y : ℕ → ℕ → ℝ) (hxy : POL n p x y) :
    ∀ t ∈ Icc 2 n, slackLP p x t = polD p x y t := by sorry

end RobustSPUA
