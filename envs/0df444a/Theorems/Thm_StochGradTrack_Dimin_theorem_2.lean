-- Prove2me | Theorems.Thm_StochGradTrack_Dimin_theorem_2
-- name    : StochGradTrack.Dimin.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:46:59.281735+00:00
-- url     : https://prove2.me/theorems/784968fe-36ac-41c4-9616-956880e5525c
-- title:
--   Theorem 2, p. 418 — with α_k = θ/(m+k), E‖x̄_k−x*‖² ≤ 2θ²σ²/(n(θμ−1)(m+k)) + O(1)/(m+k)^{θμ} + O(1)/(m+k)² and E‖x_k−1x̄_k‖² ≤ O(1)/(m+k)²
-- statement:
--   Let Assumptions 1–4 hold and let $x^*$ minimize $f=\frac1n\sum_if_i$. Run DSGT (4) with the time-varying stepsize $\alpha_k=\theta/(m+k)$, where $\theta>1/\mu$ and $m$ satisfies
--   $$\begin{cases} m>\max\Big\{\frac\theta2(\mu+L),\ \frac{4\theta L\rho_w^2+2\theta L\rho_w\sqrt{1+3\rho_w^2}}{1-\rho_w^2}\Big\},\\[4pt] \frac{(1-\rho_w^2)^2}{\theta^2(1+\rho_w^2)\rho_w^2}\Big[\frac{1-\rho_w^2}2-\frac{2m+1}{(m+1)^2}\Big]>\frac1{\theta\mu-1}\Big(\frac1\mu+\frac\theta m\Big)\frac{4\theta^2L^5}{m^3}+\frac{2C}{m^2},\end{cases}\tag{14}$$
--   with $C=\Big[\Big(\frac{1-\rho_w^2}{2\rho_w^2}-\frac{4\theta L}{m}-\frac{2\theta^2L^2}{m^2}\Big)^{-1}+2\Big]\|\mathbf W-\mathbf I\|^2L^2+\frac{3\theta L^3}{m}$. Here $\rho_w$ is the spectral norm of $\mathbf W-\frac1n\mathbf 1\mathbf 1^\top$, assumed positive. Then the squared errors are integrable, and there are constants $C_1,C_2,C_3$, independent of $k$, such that for all $k\ge0$
--   $$\mathbb E\|\bar x_k-x^*\|^2\le\frac{2\theta^2\sigma^2}{n(\theta\mu-1)(m+k)}+\frac{C_1}{(m+k)^{\theta\mu}}+\frac{C_2}{(m+k)^2},\qquad \mathbb E\|\mathbf x_k-\mathbf 1\bar x_k\|^2\le\frac{C_3}{(m+k)^2}.$$
--
--   The leading term does not depend on the network and matches centralized stochastic gradient descent with stepsize $\theta/(m+k)$ up to constant factors: averaged over agents, DSGT attains the $O(1/k)$ rate.
--
--   **Formalization Note** The page's $\mathcal O_k(1)$ are existential constants chosen after all the data (network, functions, oracle, starting point, $\theta$, $m$) and before $k$. The page cites Assumptions 1 and 2; the standing Assumptions 3–4 on $\mathbf W$ are added, since $\rho_w<1$ (Lemma 1) rests on them. $\rho_w>0$ is added because (14) and $C$ divide by $\rho_w^2$. Neither $3\theta L\le m$ nor $\theta\mu\ne2$, which parts of the printed proof need, is assumed. The powers $(m+k)^{\theta\mu}$ are real powers; $\|\mathbf x_k-\mathbf 1\bar x_k\|^2$ is the Frobenius sum $\sum_i\|x_{i,k}-\bar x_k\|^2$.
-- source:
--   Pu & Nedić, Math. Program. 187 (2021), Theorem 2 with (14)–(15), p. 418

import Mathlib
import Definitions.Def_StochGradTrack_Dimin_Model
import Definitions.Def_StochGradTrack_Dimin_StepSystem

open MeasureTheory ProbabilityTheory

namespace StochGradTrack.Dimin

/-- Theorem 2 (p. 418): with stepsizes `α_k = θ/(m + k)`, `θ > 1/μ` and `m` satisfying (14), the
mean-square errors obey (15a) and (15b) with constants independent of `k`. -/
theorem theorem_2
    {n p d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Fin n → E p → ℝ) (gradf : Fin n → E p → E p) (μ L : ℝ)
    (g : Fin n → E p → E d → E p) (ξ : ℕ → Fin n → Ω → E d) (σ : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (xstar : E p) (x0 : Fin n → E p)
    (hA1 : Assumption1 P gradf g ξ σ) (hA2 : Assumption2 f gradf μ L) (hA34 : Assumption34 W)
    (hxstar : IsMinimizer f xstar)
    (ρ : ℝ) (hρdef : ρ = rhoW W) (hρ : 0 < ρ)
    (w : ℝ) (hw : w = frobNorm (W - 1))
    (θ m : ℝ) (hθ : 1 / μ < θ)
    (hm1 : max (θ / 2 * (μ + L))
      ((4 * θ * L * ρ ^ 2 + 2 * θ * L * ρ * Real.sqrt (1 + 3 * ρ ^ 2)) / (1 - ρ ^ 2)) < m)
    (hm2 : (1 - ρ ^ 2) ^ 2 / (θ ^ 2 * (1 + ρ ^ 2) * ρ ^ 2) * ((1 - ρ ^ 2) / 2 - (2 * m + 1) / (m + 1) ^ 2)
      > 1 / (θ * μ - 1) * (1 / μ + θ / m) * (4 * θ ^ 2 * L ^ 5 / m ^ 3) + 2 * Cconst θ m L ρ w / m ^ 2) :
    (∀ k : ℕ, Integrable (fun ω => ‖avg (xs (stepDimin θ m) W g ξ x0 k ω) - xstar‖ ^ 2) P ∧
      Integrable (fun ω => consErr (xs (stepDimin θ m) W g ξ x0 k ω)) P) ∧
    ∃ C₁ C₂ C₃ : ℝ, ∀ k : ℕ,
      ∫ ω, ‖avg (xs (stepDimin θ m) W g ξ x0 k ω) - xstar‖ ^ 2 ∂P
          ≤ 2 * θ ^ 2 * σ ^ 2 / (n * (θ * μ - 1) * (m + k)) + C₁ / (m + k) ^ (θ * μ)
            + C₂ / (m + k) ^ 2 ∧
        ∫ ω, consErr (xs (stepDimin θ m) W g ξ x0 k ω) ∂P ≤ C₃ / (m + k) ^ 2 := by sorry

end StochGradTrack.Dimin
