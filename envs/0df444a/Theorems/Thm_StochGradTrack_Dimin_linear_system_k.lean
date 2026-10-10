-- Prove2me | Theorems.Thm_StochGradTrack_Dimin_linear_system_k
-- name    : StochGradTrack.Dimin.linear_system_k
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:44:36.039826+00:00
-- url     : https://prove2.me/theorems/af853dc0-237d-46ea-b1a4-404f28d05018
-- title:
--   (29)–(30), p. 425 — with α_k = θ/(m+k), (E‖x̄_{k+1}−x*‖², E‖x_{k+1}−1x̄_{k+1}‖², E‖y_{k+1}−1ȳ_{k+1}‖²) ≤ A_k(·)_k + (α_k²σ²/n, 0, M_k)
-- statement:
--   Consider DSGT (4) under Assumptions 1–4 with stepsizes $\alpha_k=\theta/(m+k)$, $\theta>0$, $m>0$, and write
--   $$U_k=\mathbb E\|\bar x_k-x^*\|^2,\qquad X_k=\mathbb E\|\mathbf x_k-\mathbf 1\bar x_k\|^2,\qquad Y_k=\mathbb E\|\mathbf y_k-\mathbf 1\bar y_k\|^2 .$$
--   Assume $\rho_w>0$, and fix an index $k$ with $\alpha_k<2/(\mu+L)$, $\beta_k>0$ and $3\alpha_kL\le1$. Then all of $U_j,X_j,Y_j$ are expectations of integrable random variables, and componentwise
--   $$\begin{bmatrix}U_{k+1}\\X_{k+1}\\Y_{k+1}\end{bmatrix}\le\mathbf A_k\begin{bmatrix}U_k\\X_k\\Y_k\end{bmatrix}+\begin{bmatrix}\alpha_k^2\sigma^2/n\\0\\M_k\end{bmatrix},$$
--   with $\mathbf A_k$, $\beta_k$ and $M_k$ as in (29)–(30) and $w=\|\mathbf W-\mathbf I\|$.
--
--   This is the time-varying analogue of the linear system (21) and drives the whole proof of Theorem 2.
--
--   **Formalization Note** The hypothesis $3\alpha_kL\le1$ is not on the page: the derivation of Lemma 4 (20), which (29) reuses at $\alpha=\alpha_k$, simplifies $3\alpha^2nL^4+\alpha nL^3$ to $2\alpha nL^3$ and $2\alpha L^3+3\alpha^2L^4$ to $3\alpha L^3$ (p. 445), which needs $\alpha L\le 1/3$. The page states (29) under $m>\frac\theta2(\mu+L)$, which gives $\alpha_k<2/(\mu+L)$ for every $k$; the statement is per index $k$. $\rho_w>0$ is needed for $\beta_k$ and $\mathbf A_k$ to be defined.
-- source:
--   Pu & Nedić, Math. Program. 187 (2021), §3.3, (29) and (30), p. 425; Lemma 4 (18)–(20), p. 420, with its proof on p. 445

import Mathlib
import Definitions.Def_StochGradTrack_Dimin_Model
import Definitions.Def_StochGradTrack_Dimin_StepSystem

open MeasureTheory ProbabilityTheory

namespace StochGradTrack.Dimin

/-- (29)–(30) (p. 425): at every `k` with `α_k < 2/(μ+L)`, `β_k > 0` and (disclosed) `3 α_k L ≤ 1`, the
vector `(U_k, X_k, Y_k)` of mean-square errors satisfies `V_{k+1} ≤ A_k V_k + (α_k²σ²/n, 0, M_k)`
componentwise. -/
theorem linear_system_k
    {n p d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Fin n → E p → ℝ) (gradf : Fin n → E p → E p) (μ L : ℝ)
    (g : Fin n → E p → E d → E p) (ξ : ℕ → Fin n → Ω → E d) (σ : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (xstar : E p) (x0 : Fin n → E p)
    (hA1 : Assumption1 P gradf g ξ σ) (hA2 : Assumption2 f gradf μ L) (hA34 : Assumption34 W)
    (hxstar : IsMinimizer f xstar)
    (ρ : ℝ) (hρdef : ρ = rhoW W) (hρ : 0 < ρ)
    (w : ℝ) (hw : w = frobNorm (W - 1))
    (θ m : ℝ) (hθ : 0 < θ) (hm : 0 < m) (k : ℕ)
    (hk1 : stepDimin θ m k < 2 / (μ + L)) (hk2 : 0 < betaK θ m L ρ k)
    (hk3 : 3 * stepDimin θ m k * L ≤ 1) :
    let U : ℕ → ℝ := fun j => ∫ ω, ‖avg (xs (stepDimin θ m) W g ξ x0 j ω) - xstar‖ ^ 2 ∂P
    let X : ℕ → ℝ := fun j => ∫ ω, consErr (xs (stepDimin θ m) W g ξ x0 j ω) ∂P
    let Y : ℕ → ℝ := fun j => ∫ ω, consErr (ys (stepDimin θ m) W g ξ x0 j ω) ∂P
    (∀ j : ℕ, Integrable (fun ω => ‖avg (xs (stepDimin θ m) W g ξ x0 j ω) - xstar‖ ^ 2) P ∧
      Integrable (fun ω => consErr (xs (stepDimin θ m) W g ξ x0 j ω)) P ∧
      Integrable (fun ω => consErr (ys (stepDimin θ m) W g ξ x0 j ω)) P) ∧
    ∀ i : Fin 3, ![U (k + 1), X (k + 1), Y (k + 1)] i
      ≤ Matrix.mulVec (Ak θ m μ L n ρ w k) ![U k, X k, Y k] i + bk θ m L n σ k i := by sorry

end StochGradTrack.Dimin
