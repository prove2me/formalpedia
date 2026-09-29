-- Prove2me | Theorems.Thm_PolyakJuditsky_Averaging_averaged_sa_asymptotic_normality
-- name    : PolyakJuditsky.Averaging.averaged_sa_asymptotic_normality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T23:42:21.864301+00:00
-- url     : https://prove2.me/theorems/18420cfb-4829-40ea-93e9-ae07287437b0
-- title:
--   Theorem 2 — averaged stochastic approximation: $\bar x_t\to x^*$ a.s. and $\sqrt t(\bar x_t-x^*)\xrightarrow{D}N(0,G^{-1}S(G^{-1})^T)$
-- statement:
--   Let $R:\mathbb R^N\to\mathbb R^N$ be continuous with root $x^*$, and let $(\Omega,\mathcal F,(\mathcal F_t),P)$ be a filtered probability space carrying disturbances $(\xi_t)_{t\ge1}$. Suppose:
--
--   1. (Assumption 3.1) there is a differentiable Lyapunov function $V$ with $V(x)\ge\alpha|x|^2$, $L$-Lipschitz gradient, $V(0)=0$, $\nabla V(x-x^*)^TR(x)>0$ for $x\ne x^*$ and $\nabla V(x-x^*)^TR(x)\ge\lambda_1V(x-x^*)$ near $x^*$;
--   2. (Assumption 3.2) $|R(x)-G(x-x^*)|\le K_1|x-x^*|^{1+\lambda}$ near $x^*$ for a matrix $G$ whose eigenvalues have positive real part, $0<\lambda\le1$;
--   3. (Assumption 3.3) $\xi_t$ is a square-integrable martingale difference with $E(|\xi_t|^2\mid\mathcal F_{t-1})+|R(x_{t-1})|^2\le K_2(1+|x_{t-1}|^2)$, and $\xi_t=\xi_t(0)+\zeta_t$ where $\xi_t(0)$ is a martingale difference with conditional covariance tending to $S\succ0$ in probability and uniformly integrable conditional second moments, and $E(|\zeta_t|^2\mid\mathcal F_{t-1})\le\delta(x_{t-1}-x^*)$ for large $t$ with $\delta(x)\to0$ as $x\to0$;
--   4. (Assumption 3.4) $\gamma_t>0$, $(\gamma_t-\gamma_{t+1})/\gamma_t=o(\gamma_t)$, $\sum_t\gamma_t^{(1+\lambda)/2}t^{-1/2}<\infty$, and (added) $\gamma_t\to0$, $\sum_t\gamma_t^2<\infty$.
--
--   (Precise forms are in the definition file.) Let $x_t=x_{t-1}-\gamma_t(R(x_{t-1})+\xi_t)$ from a nonrandom $x_0$, and $\bar x_t=\frac1t\sum_{i=0}^{t-1}x_i$ (algorithm (7)). Then $\bar x_t\to x^*$ almost surely, and
--   $$\sqrt t\,(\bar x_t-x^*)\xrightarrow{D}N(0,V),\qquad V=G^{-1}S(G^{-1})^T.\tag{11}$$
--
--   Averaging the iterates of a stochastic approximation scheme with slowly decreasing steps attains the asymptotic covariance $G^{-1}S(G^{-1})^T$ of the optimal scheme $x_t=x_{t-1}-t^{-1}R'(x^*)^{-1}y_t$, without knowing $R'(x^*)$.
--
--   **Formalization Note** Corrections of the printed assumptions (each used by the paper's proof) are listed in the definition file: $V(0)=0$ and $\lambda_1V(x-x^*)$ in 3.1; the ungarbled Eq. (10); $\delta(x_{t-1}-x^*)$ in 3.3; and the added hypotheses $\gamma_t\to0$, $\sum\gamma_t^2<\infty$ of 3.4, used on p. 849 but not implied by 3.4. $R$ is assumed continuous. The paper states no regularity of $R$, but its proof needs $\nabla V(x-x^*)^TR(x)$ to be bounded away from $0$ on every annulus $\varepsilon\le|x-x^*|\le\rho$ (the constant $\alpha$ of (A13) on the ball $|\Delta|\le R$, and the step "almost sure convergence of the algorithm follows from Parts 1 and 2", pp. 849–850). Continuity together with Assumption 3.1 gives this; with $R$ only measurable, a root-free $R$ whose drift degenerates at one point off $x^*$ can trap the iterates there with positive probability. Convergence in distribution is to the Gaussian measure on $\mathbb R^N$ with mean $0$ and covariance $V$, which is positive definite under these hypotheses.
-- source:
--   Polyak, Juditsky, Acceleration of stochastic approximation by averaging, SIAM J. Control Optim. 30 (1992), p. 841, Theorem 2, Eq. (11); p. 840, Eq. (7), Assumptions 3.1, 3.2; p. 841, Assumptions 3.3, 3.4

import Mathlib
import Definitions.Def_PolyakJuditsky_Averaging_Model
import Definitions.Def_PolyakJuditsky_Averaging_Assumptions

open MeasureTheory ProbabilityTheory Filter Topology

namespace PolyakJuditsky.Averaging

/-- Theorem 2 (p. 841): under Assumptions 3.1–3.4 (in the corrected and completed form of the
definitions `LyapunovAssumption`, `LinearizationAssumption`, `NoiseAssumption`,
`StepAssumption`), the averaged iterate `x̄_t` of Eq. (7) converges to `x*` almost surely and
`√t (x̄_t - x*) → N(0, V)` in distribution with `V = G⁻¹ S (G⁻¹)ᵀ` (Eq. (11)).
`R` is assumed continuous (the paper states no regularity of `R`; its proof needs
`⟪∇V(x - x*), R x⟫` bounded away from `0` on every annulus `ε ≤ |x - x*| ≤ ρ`, p. 849–850,
which continuity and Assumption 3.1 give). -/
theorem averaged_sa_asymptotic_normality {N : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (x₀ xstar : EuclideanSpace ℝ (Fin N)) (γ : ℕ → ℝ)
    (R : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (ξ ξ0 : ℕ → Ω → EuclideanSpace ℝ (Fin N)) (V : EuclideanSpace ℝ (Fin N) → ℝ)
    (G S : Matrix (Fin N) (Fin N) ℝ) (lam : ℝ)
    (hR : Continuous R) (h31 : LyapunovAssumption R xstar V)
    (h32 : LinearizationAssumption R xstar G lam)
    (h33 : NoiseAssumption P ℱ x₀ γ R ξ ξ0 xstar S) (h34 : StepAssumption γ lam) :
    (∀ᵐ ω ∂P, Tendsto (fun t => saAverage x₀ γ R ξ t ω) atTop (𝓝 xstar)) ∧
    TendstoInDistribution
      (fun (t : ℕ) (ω : Ω) => Real.sqrt t • (saAverage x₀ γ R ξ t ω - xstar))
      atTop id (fun _ => P) (multivariateGaussian 0 (G⁻¹ * S * (G⁻¹).transpose)) := by sorry

end PolyakJuditsky.Averaging
