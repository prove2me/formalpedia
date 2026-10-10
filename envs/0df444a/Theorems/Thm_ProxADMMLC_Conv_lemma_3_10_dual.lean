-- Prove2me | Theorems.Thm_ProxADMMLC_Conv_lemma_3_10_dual
-- name    : ProxADMMLC.Conv.lemma_3_10_dual
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:48:23.119742+00:00
-- url     : https://prove2.me/theorems/6a76cc61-1bb4-48f5-8d7a-ca850f4d6061
-- title:
--   Lemma 3.10 (3.15), p. 2282 — local dual error bound dist(y, Y*(z)) ≤ σ₅‖Ax(y, z) − b‖
-- statement:
--   Suppose Assumption 2.2 (a)–(c) holds, $\gamma$ satisfies (2.4), and $\Gamma>0$, $p>0$, $p>-\gamma$. Let $x(y,z)$ and $x^*(z)$ be the minimizers (2.7) and (2.9), and let $Y^*(z)$ be the set of dual multipliers of problem (2.8). Fix $y^0\in\mathbb R^m$. Then there are positive scalars $\Delta$ and $\sigma_5$ such that
--   $$\operatorname{dist}\big(y,Y^*(z)\big)\ \le\ \sigma_5\,\|Ax(y,z)-b\|\tag{3.15}$$
--   whenever $y\in y^0+\operatorname{range}(A)$, $z\in P$, $\|Ax(y,z)-b\|\le\Delta$ and $\operatorname{dist}(z,X^*)\le\Delta$.
--
--   This local dual error bound is the step where strict complementarity enters the convergence proof: it bounds the distance of the dual iterate to the multipliers of the proximal problem by the primal residual, which controls the negative term of the potential in Case 1 of (3.37).
--
--   **Formalization Note** $y^0$ is the algorithm's initial dual vector on the page; the statement holds for every fixed $y^0$, with $\Delta,\sigma_5$ chosen after it. The page leaves the location of $z$ implicit; its proof (through Lemma 3.4) uses $z\in P$, and every application has $z=z^t\in P$, so $z\in P$ is added. $Y^*(z)$ is nonempty (multipliers of a linearly constrained strongly convex problem exist), so `Metric.infDist` to the empty set never decides the statement.
-- source:
--   Zhang & Luo, A proximal alternating direction method of multiplier for linearly constrained nonconvex minimization, SIAM J. Optim. 30(3) (2020), p. 2282, Lemma 3.10, (3.15) (proof pp. 2282–2284)

import Mathlib
import Definitions.Def_ProxADMMLC_Conv_Setting

namespace ProxADMMLC.Conv

theorem lemma_3_10_dual {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ)
    (hℓu : ∀ i, ℓ i < u i) (L : ℝ) (hA : Assumption22 f A b ℓ u L) (γ : ℝ)
    (hγ : MonoConst f ℓ u γ) (Γ p : ℝ) (hΓ : 0 < Γ) (hp : 0 < p) (hpγ : -γ < p)
    (xs : E m → E n → E n) (hxs : IsXSel f A b ℓ u Γ p xs)
    (xst : E n → E n) (hxst : IsXStarSel f A b ℓ u p xst) :
    ∀ y0 : E m, ∃ Δ σ5 : ℝ, 0 < Δ ∧ 0 < σ5 ∧ ∀ (y : E m) (z : E n),
      y - y0 ∈ LinearMap.range (A : E n →ₗ[ℝ] E m) → z ∈ box ℓ u → ‖A (xs y z) - b‖ ≤ Δ →
        Metric.infDist z (Xstar f A b ℓ u) ≤ Δ →
          Metric.infDist y (Ystar f A ℓ u p xst z) ≤ σ5 * ‖A (xs y z) - b‖ := by sorry

end ProxADMMLC.Conv
