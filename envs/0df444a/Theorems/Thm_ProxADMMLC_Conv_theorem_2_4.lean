-- Prove2me | Theorems.Thm_ProxADMMLC_Conv_theorem_2_4
-- name    : ProxADMMLC.Conv.theorem_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:47:48.1432+00:00
-- url     : https://prove2.me/theorems/5fcba70d-6ab6-4243-9fd7-3896c1f1b528
-- title:
--   Theorem 2.4, p. 2277 — with small stepsizes, Algorithm 2.2 has bounded duals, its iterates approach X* and W, and its limit points are KKT pairs
-- statement:
--   Consider $\min f(x)$ subject to $Ax=b$, $x\in P$, where $P=\{x:\ell_i\le x_i\le u_i\}$ with $\ell_i<u_i$, and run Algorithm 2.2:
--   $$y^{t+1}=y^t+\alpha(Ax^t-b),\quad x^{t+1}=[x^t-c\nabla_xK(x^t,z^t;y^{t+1})]_+,\quad z^{t+1}=z^t+\beta(x^{t+1}-z^t),$$
--   from $x^0,z^0\in P$ and $y^0\in\mathbb R^m$, where $K(x,z;y)=f(x)+y^\top(Ax-b)+\frac\Gamma2\|Ax-b\|^2+\frac p2\|x-z\|^2$.
--
--   Suppose Assumption 2.2 holds (the origin is in the relative interior of $AP-b$, strict complementarity holds, and $\nabla f$ is $L$-Lipschitz on $P$), $\gamma$ satisfies (2.4), and the parameters satisfy $\Gamma>0$, $p>0$, $p>-\gamma$ and $0<c<1/L_K$ with $L_K=L+p+\Gamma\|A\|^2$. Then the stepsizes can be chosen sufficiently small: there is $\alpha_0>0$ such that for every $\alpha\in(0,\alpha_0)$ and every $y^0$ there is $\beta_0>0$ such that for every $\beta\in(0,1]$ with $\beta\le\beta_0$, every run from $y^0$ satisfies:
--   1. the dual iterates $\{y^t\}$ are bounded;
--   2. $\displaystyle\lim_{t\to\infty}\|x^{t+1}-x^t\|=0$;
--   3. $\displaystyle\lim_{t\to\infty}\operatorname{dist}(x^t,X^*)=0$ and $\displaystyle\lim_{t\to\infty}\operatorname{dist}(z^t,X^*)=0$;
--   4. $\displaystyle\lim_{t\to\infty}\operatorname{dist}\big((x^t,y^t),W\big)=0$;
--   5. every limit point of $\{(x^t,y^t)\}$ is a primal-dual stationary pair of (1.1), i.e. lies in $W$.
--
--   This is the paper's main result: the proximal term centred at the exponentially averaged sequence $z^t$ stabilizes the inexact augmented Lagrangian method and gives global convergence to KKT points for a nonconvex objective.
--
--   **Formalization Note** "Sufficiently small" is the quantifier order $\exists\alpha_0\,\forall\alpha\,\forall y^0\,\exists\beta_0\,\forall\beta$ and then all runs; $\alpha_0$ depends only on the problem data and $\Gamma,p,c,L,\gamma$, and $\beta_0$ in addition on $\alpha$ and $y^0$ (the proof uses error bounds stated for a fixed $y^0+\operatorname{range}(A)$), never on $x^0,z^0$ or the run. $\operatorname{dist}((x,y),W)$ is computed with the maximum of the two Euclidean distances (the product metric of Lean), which is equivalent to the Euclidean distance on $\mathbb R^{n+m}$, so the limit is the page's. A limit point is a cluster point (`MapClusterPt`). $X^*$ and $W$ are nonempty under the hypotheses (a global minimizer over the nonempty compact feasible set is a KKT point), so the distances are not junk values.
-- source:
--   Zhang & Luo, A proximal alternating direction method of multiplier for linearly constrained nonconvex minimization, SIAM J. Optim. 30(3) (2020), p. 2277, Theorem 2.4

import Mathlib
import Definitions.Def_ProxADMMLC_Conv_Setting

open Filter Topology

namespace ProxADMMLC.Conv

theorem theorem_2_4 {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ)
    (hℓu : ∀ i, ℓ i < u i) (L : ℝ) (hA : Assumption22 f A b ℓ u L) (γ : ℝ)
    (hγ : MonoConst f ℓ u γ) (Γ p c : ℝ) (hΓ : 0 < Γ) (hp : 0 < p) (hc : 0 < c)
    (hcL : c * (L + p + Γ * ‖A‖ ^ 2) < 1) (hpγ : -γ < p) :
    ∃ α₀ > 0, ∀ α, 0 < α → α < α₀ → ∀ y0 : E m, ∃ β₀ > 0, ∀ β, 0 < β → β ≤ 1 → β ≤ β₀ →
      ∀ (x z : ℕ → E n) (y : ℕ → E m), IsRun f A b ℓ u Γ p c α β x y z → y 0 = y0 →
        Bornology.IsBounded (Set.range y) ∧
        Tendsto (fun t => ‖x (t + 1) - x t‖) atTop (𝓝 0) ∧
        Tendsto (fun t => Metric.infDist (x t) (Xstar f A b ℓ u)) atTop (𝓝 0) ∧
        Tendsto (fun t => Metric.infDist (z t) (Xstar f A b ℓ u)) atTop (𝓝 0) ∧
        Tendsto (fun t => Metric.infDist (x t, y t) (Wset f A b ℓ u)) atTop (𝓝 0) ∧
        ∀ q : E n × E m, MapClusterPt q atTop (fun t => (x t, y t)) → q ∈ Wset f A b ℓ u := by sorry

end ProxADMMLC.Conv
