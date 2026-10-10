-- Prove2me | Theorems.Thm_ProxADMMLC_Conv_cor_3_7
-- name    : ProxADMMLC.Conv.cor_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:47:45.323046+00:00
-- url     : https://prove2.me/theorems/3ab9c162-5ab1-49ae-bdb6-3d1fd0214ddd
-- title:
--   Corollary 3.7, p. 2281 — small ‖x − x⁺‖, ‖z − x⁺‖, ‖Ax(y⁺, z) − b‖ imply x, z within ε of X*
-- statement:
--   Suppose Assumption 2.2(a) and (c) hold, $\gamma$ satisfies (2.4), and $\Gamma>0$, $p>0$, $p>-\gamma$, $\alpha>0$, $0<c<1/L_K$ with $L_K=L+p+\Gamma\|A\|^2$. Let $x(y,z)$ be the minimizer (2.7) and $x^+$, $y^+$ the updates (3.7)–(3.8). Fix $\tilde y^0\in\mathbb R^m$. For every $\varepsilon>0$ there is $\delta(\varepsilon)>0$ such that for all $x,z\in P$ and all $y\in\tilde y^0+\operatorname{range}(A)$,
--   $$\max\{\|x-x^+\|,\ \|z-x^+\|,\ \|Ax(y^+,z)-b\|\}<\delta(\varepsilon)\quad\Longrightarrow\quad\max\{\operatorname{dist}(x,X^*),\ \operatorname{dist}(z,X^*)\}<\varepsilon.$$
--
--   Once the residuals of (3.37) vanish, this corollary converts them into convergence of $x^t$ and $z^t$ to the stationary set, which is the conclusion of Theorem 2.4.
--
--   **Formalization Note** $\delta$ depends on $\tilde y^0$ and $\varepsilon$ and is chosen before $x,z,y$. Assumption 2.2(b) is not used. $\operatorname{dist}$ is `Metric.infDist`; $X^*$ is nonempty under these hypotheses, so a distance to the empty set never decides the statement.
-- source:
--   Zhang & Luo, A proximal alternating direction method of multiplier for linearly constrained nonconvex minimization, SIAM J. Optim. 30(3) (2020), p. 2281, Corollary 3.7 (proof in Appendix A, p. 2300)

import Mathlib
import Definitions.Def_ProxADMMLC_Conv_Setting

namespace ProxADMMLC.Conv

theorem cor_3_7 {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ)
    (hℓu : ∀ i, ℓ i < u i) (ha : Assump22a A b ℓ u) (L : ℝ) (hf : Assump22c f ℓ u L)
    (γ : ℝ) (hγ : MonoConst f ℓ u γ) (Γ p c α : ℝ) (hΓ : 0 < Γ) (hp : 0 < p) (hc : 0 < c)
    (hcL : c * (L + p + Γ * ‖A‖ ^ 2) < 1) (hpγ : -γ < p) (hα : 0 < α)
    (xs : E m → E n → E n) (hxs : IsXSel f A b ℓ u Γ p xs) :
    ∀ y0 : E m, ∀ ε > 0, ∃ δ > 0, ∀ x ∈ box ℓ u, ∀ z ∈ box ℓ u, ∀ y : E m,
      y - y0 ∈ LinearMap.range (A : E n →ₗ[ℝ] E m) →
      max (max ‖x - xPlus f A b ℓ u Γ p c α x z y‖ ‖z - xPlus f A b ℓ u Γ p c α x z y‖)
          ‖A (xs (yPlus A b α x y) z) - b‖ < δ →
        max (Metric.infDist x (Xstar f A b ℓ u)) (Metric.infDist z (Xstar f A b ℓ u)) < ε := by sorry

end ProxADMMLC.Conv
