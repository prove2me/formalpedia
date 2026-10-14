-- Prove2me | Theorems.Thm_RobustSPA_AllDist_revenue_under_Fstar
-- name    : RobustSPA.AllDist.revenue_under_Fstar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:47.057135+00:00
-- url     : https://prove2.me/theorems/b9c4f38f-6236-484a-8221-e9b5fa987e75
-- title:
--   Proof of Proposition 4, p. App-8 — expected revenue of a DSIC mechanism under F* is at most (1/n) Σ_k (r* x_k(e_k) − ∫₀^{r*} x_k(t e_k) dt)
-- statement:
--   Let $n \ge 1$, $r^* = 1/e$, and let $G$ be the isorevenue law on $[1/e, 1]$: its CDF is $0$ below $1/e$, $1 - \frac{1}{e t}$ on $[1/e, 1)$ and $1$ at $1$. Let $\mathbf F^* = \frac1n\sum_{k=1}^n \mathbf F^{*,k}$, where under $\mathbf F^{*,k}$ buyer $k$ has value $t \sim G$ and all other buyers have value $0$. Write $e_k$ for the $k$-th unit vector. For every DSIC mechanism $(x, p) \in \mathcal M$,
--   $$\mathbb E_{v \sim \mathbf F^*}\Big[\sum_{i=1}^n p_i(v)\Big] \le \frac1n \sum_{k=1}^n \Big( r^*\, x_k(e_k) - \int_0^{r^*} x_k(\tilde v_k\, e_k)\, d\tilde v_k \Big),$$
--   with equality whenever every buyer with valuation $0$ pays nothing, i.e. $p_i(v) = 0$ for all $i$ and all $v \in [0,1]^n$ with $v_i = 0$.
--
--   Since $0 \le x_k \le 1$, the right side is at most $r^* = 1/e$, with equality exactly when each $x_k(e_k) = 1$ and $x_k(\tilde v_k e_k) = 0$ for $\tilde v_k < r^*$; this is how the paper shows that $\mathrm{SPA}(\Phi^*)$ maximizes revenue under $\mathbf F^*$, the half $R_n(m^*, \mathbf F^*) \le R_n(m, \mathbf F^*)$ of the saddle inequality.
--
--   **Formalization Note** The page writes an equality, after setting $p_i(0, v_{-i}) = 0$ "because the seller aims to maximize revenue" (App-3). For a general DSIC mechanism individual rationality only gives $p_i \le 0$ at $v_i = 0$, both for $p_k(0)$ in Myerson's payment identity and for the payments of the buyers $i \ne k$ with value $0$ under $\mathbf F^{*,k}$; the statement therefore asserts the inequality, and the page's equality under the page's normalization. The isorevenue law is given through its CDF.
-- source:
--   Anunrojwong, Balseiro & Besbes, On the Robustness of Second-Price Auctions in Prior-Independent Mechanism Design, arXiv:2204.10478v5, p. App-8, Proof of Proposition 4 (revenue display); p. App-3 (Myerson's payment characterization, p_i(0, v_{-i}) = 0)

import Mathlib
import Definitions.Def_RobustSPA_AllDist_Setting
open MeasureTheory

namespace RobustSPA.AllDist

/-- Proof of Proposition 4, p. App-8: expected revenue of a DSIC mechanism under `F*`. -/
theorem revenue_under_Fstar (n : ℕ) (hn : 0 < n) (G : ProbabilityMeasure ℝ)
    (hG : ∀ t, cdfOf G t = isoCDF (Real.exp (-1)) t) (m : Mechanism n) (hm : m.IsDSIC) :
    ∫ v, ∑ i, m.p i v ∂(Fstar n (G : Measure ℝ))
        ≤ (1 / (n : ℝ)) * ∑ k : Fin n, (Real.exp (-1) * m.x k (Pi.single k 1)
            - ∫ t in (0 : ℝ)..(Real.exp (-1)), m.x k (Pi.single k t)) ∧
    ((∀ i, ∀ v ∈ cube n, v i = 0 → m.p i v = 0) →
      ∫ v, ∑ i, m.p i v ∂(Fstar n (G : Measure ℝ))
        = (1 / (n : ℝ)) * ∑ k : Fin n, (Real.exp (-1) * m.x k (Pi.single k 1)
            - ∫ t in (0 : ℝ)..(Real.exp (-1)), m.x k (Pi.single k t))) := by sorry

end RobustSPA.AllDist
