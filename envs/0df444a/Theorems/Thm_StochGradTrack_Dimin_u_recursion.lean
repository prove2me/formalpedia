-- Prove2me | Theorems.Thm_StochGradTrack_Dimin_u_recursion
-- name    : StochGradTrack.Dimin.u_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:44:52.631677+00:00
-- url     : https://prove2.me/theorems/521af363-915c-45ed-bbfd-833e67a7ab51
-- title:
--   p. 427 — U(k+1) ≤ (1 − α_kμ)U_k + (2α_kL²/(μn))X_k + α_k²σ²/n
-- statement:
--   Consider DSGT (4) under Assumptions 1–4 with stepsizes $\alpha_k=\theta/(m+k)$, where $\theta>0$ and $m>\frac\theta2(\mu+L)$. Let $U_k=\mathbb E\|\bar x_k-x^*\|^2$ and $X_k=\mathbb E\|\mathbf x_k-\mathbf 1\bar x_k\|^2$. Then both are expectations of integrable random variables and, for every $k\ge0$,
--   $$U_{k+1}\le(1-\alpha_k\mu)U_k+\frac{2\alpha_kL^2}{\mu n}X_k+\frac{\alpha_k^2\sigma^2}{n}.$$
--
--   Combined with $X_k\le\hat X/(m+k)^2$, unrolling this recursion yields the leading term $2\theta^2\sigma^2/(n(\theta\mu-1)(m+k))$ of Theorem 2.
--
--   **Formalization Note** This is the first row of (29), which comes from Lemma 4 (18) and needs neither $\rho_w>0$ nor $3\alpha_kL\le1$; the factor $1+\alpha_k\mu$ is bounded by $2$.
-- source:
--   Pu & Nedić, Math. Program. 187 (2021), §3.3, p. 427 (first display)

import Mathlib
import Definitions.Def_StochGradTrack_Dimin_Model
import Definitions.Def_StochGradTrack_Dimin_StepSystem

open MeasureTheory ProbabilityTheory

namespace StochGradTrack.Dimin

/-- The refined `U` recursion (p. 427): for `α_k = θ/(m+k)` with `m > (θ/2)(μ+L)`,
`U_{k+1} ≤ (1 − α_kμ) U_k + (2α_kL²/(μn)) X_k + α_k²σ²/n` for every `k`. -/
theorem u_recursion
    {n p d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Fin n → E p → ℝ) (gradf : Fin n → E p → E p) (μ L : ℝ)
    (g : Fin n → E p → E d → E p) (ξ : ℕ → Fin n → Ω → E d) (σ : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (xstar : E p) (x0 : Fin n → E p)
    (hA1 : Assumption1 P gradf g ξ σ) (hA2 : Assumption2 f gradf μ L) (hA34 : Assumption34 W)
    (hxstar : IsMinimizer f xstar)
    (θ m : ℝ) (hθ : 0 < θ) (hm : θ / 2 * (μ + L) < m) :
    let U : ℕ → ℝ := fun j => ∫ ω, ‖avg (xs (stepDimin θ m) W g ξ x0 j ω) - xstar‖ ^ 2 ∂P
    let X : ℕ → ℝ := fun j => ∫ ω, consErr (xs (stepDimin θ m) W g ξ x0 j ω) ∂P
    (∀ j : ℕ, Integrable (fun ω => ‖avg (xs (stepDimin θ m) W g ξ x0 j ω) - xstar‖ ^ 2) P ∧
      Integrable (fun ω => consErr (xs (stepDimin θ m) W g ξ x0 j ω)) P) ∧
    ∀ k : ℕ, U (k + 1) ≤ (1 - stepDimin θ m k * μ) * U k + 2 * stepDimin θ m k * L ^ 2 / (μ * n) * X k
      + stepDimin θ m k ^ 2 * σ ^ 2 / n := by sorry

end StochGradTrack.Dimin
