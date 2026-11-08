-- Prove2me | Theorems.Thm_RobustSPUA_theorem_7_projection
-- name    : RobustSPUA.theorem_7_projection
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T12:44:13.99704+00:00
-- url     : https://prove2.me/theorems/f75cf29d-6a98-41df-b5e3-b7c36ae7c578
-- title:
--   Proof of Theorem 7, p.33 — projecting $(P')$ onto $(x,\gamma)$ gives $(LP)_{n,p}$ (corrected: recursion for $t\ge2$)
-- statement:
--   Fix $n\ge1$ and $p\in(0,1]$. For every $x$ and every real $\gamma$, there is $y$ such that $(x,y,\gamma)$ is feasible for
--   $$
--   (P')\qquad (x,y)\ge0,\quad x_{1,1}+y_{1,1}\le1,\quad x_{t,s}+y_{t,s}\le\frac1t\sum_{\sigma=1}^{t-1}\bigl(y_{t-1,\sigma}+(1-p)x_{t-1,\sigma}\bigr)\ \ (t\in\{2,\dots,n\},\ s\in[t]),
--   $$
--   $$
--   \gamma\le\frac{p\sum_{t=1}^n\sum_{s=1}^t x_{t,s}\,\mathbf P(R_t\le k\mid r_t=s)}{1-(1-p)^k}\quad(k\in[n]),
--   $$
--   if and only if $(x,\gamma)$ is feasible for $(LP)_{n,p}$:
--   $$
--   x\ge0,\quad x_{t,s}\le\frac1t\Bigl(1-p\sum_{\tau=1}^{t-1}\sum_{\sigma=1}^{\tau}x_{\tau,\sigma}\Bigr)\ \ (t\in[n],\ s\in[t]),\quad \gamma\le\frac{p}{1-(1-p)^k}\sum_{t=1}^n\sum_{s=1}^t x_{t,s}\,\mathbf P(R_t\le k\mid r_t=s)\ \ (k\in[n]).
--   $$
--
--   This is the elimination of the variables $y$ that turns $(P')$ into the linear program of Theorem 2.
--
--   **Formalization Note** In both programs $\mathbf P(R_t\le k\mid r_t=s)$ is the closed form of Theorem 2 (`rankCoef`).
--
--   Differences from the source:
--   - correction: (P′) with the constraint x_{t,s}+y_{t,s} ≤ (1/t)Σ_σ(…) for all t ∈ [n] (p.33) → that constraint for t ∈ [2, n]; reason: as printed, the t = 1 row forces x_{1,1} = y_{1,1} = 0; at n = 1, (x_{1,1}, γ) = (1, 1) is feasible for (LP)_{1,p} but is not in the projection of the printed (P′)
--   - reading: (P′) written as max over x ≥ 0 → x ≥ 0 and y ≥ 0; reason: (P′) is (P) of p.29, which maximizes over x, y ≥ 0, with the objective linearized; without y ≥ 0 the projection is not (LP)_{n,p}
--   - reading: P(R_t ≤ k | r_t = s) in (P′) and (LP)_{n,p} → the closed form of Theorem 2 (rankCoef) in both; reason: Theorem 2/7 defines the LP coefficient by that closed form; that it equals the conditional probability is the separate milestone theorem_2_rank_probability
--   - encoding: the number of candidates n, implicitly positive (the min over k ∈ [n] in (1) and the initial state (1,1) need it) → the explicit hypothesis 1 ≤ n; reason: a nondegeneracy condition that only excludes the undefined case n = 0
--   - encoding: vectors x, y and policies indexed by the states (t,s), t ∈ [n], s ∈ [t] → total real-valued functions of two natural numbers; reason: only the values at the states are constrained or read, so the instances are the same
-- source:
--   Perez-Salazar, Singh, Toriello, Robust Online Selection with Uncertain Offer Acceptance, arXiv:2112.00842v2, proof of Theorem 7, p.33 ((P′) and the sentence 'By projecting the feasible region of (P′) onto the variables (x, γ) we obtain (LP)_{n,p}')

import Mathlib
import Definitions.Def_RobustSPUA_Model
import Definitions.Def_RobustSPUA_LP

open Finset

namespace RobustSPUA

/-- S. Perez-Salazar, M. Singh, A. Toriello, *Robust Online Selection with Uncertain Offer Acceptance*, arXiv:2112.00842v2, proof of Theorem 7, p.33 (corrected: recursion for `t ≥ 2`): projecting the
feasible region of (P′) onto the variables `(x, γ)` gives the feasible region of (LP)_{n,p}.

**Formalization Note** (P′)'s constraint (19) is read for `t ∈ [2, n]` (printed `∀ t ∈ [n]`,
which forces `x_{1,1} = 0`). In both programs `P(R_t ≤ k | r_t = s)` is the closed form of
Theorem 2 (`rankCoef`). -/
theorem theorem_7_projection (n : ℕ) (hn : 1 ≤ n) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∀ (x : ℕ → ℕ → ℝ) (γ : ℝ), (∃ y, PprimeFeasible n p x y γ) ↔ LPFeasible n p x γ := by sorry

end RobustSPUA
