-- Prove2me | Theorems.Thm_StochGradTrack_Dimin_induction_bounds
-- name    : StochGradTrack.Dimin.induction_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:44:39.001979+00:00
-- url     : https://prove2.me/theorems/201a9a87-9a40-4fcb-943d-483ad89598d7
-- title:
--   (32)–(36), pp. 425–427 — U_k ≤ Û/(m+k), E‖x_k−1x̄_k‖² ≤ X̂/(m+k)², E‖y_k−1ȳ_k‖² ≤ Ŷ for all k
-- statement:
--   Assume the hypotheses of Theorem 2: Assumptions 1–4, $\rho_w>0$, $\alpha_k=\theta/(m+k)$ with $\theta>1/\mu$ and $m$ satisfying (14). Assume in addition $3\theta L\le m$. Let $U_k$, $X_k$, $Y_k$ be the mean-square errors $\mathbb E\|\bar x_k-x^*\|^2$, $\mathbb E\|\mathbf x_k-\mathbf 1\bar x_k\|^2$, $\mathbb E\|\mathbf y_k-\mathbf 1\bar y_k\|^2$, and put $X_0=\|\mathbf x_0-\mathbf 1\bar x_0\|^2$, $Y_0=\mathbb E\|\mathbf y_0-\mathbf 1\bar y_0\|^2$, $C$ as in Theorem 2, and
--   $$C_1=\frac{1-\rho_w^2}{\theta^2(1+\rho_w^2)\rho_w^2}\Big[\frac{1-\rho_w^2}2-\frac{2m+1}{(m+1)^2}\Big],\quad C_2=\frac{2C}{(1-\rho_w^2)m^2},$$
--   $$C_3=\frac2{1-\rho_w^2}\Big\{\frac{2\theta nL^3\|\bar x_0-x^*\|^2}{m}+\Big[\frac{3\theta^2L^2}{m^2}+2\Big(\frac{\theta L}m+1\Big)(n+1)\Big]\sigma^2\Big\},$$
--   $$C_4=\frac2{1-\rho_w^2}\Big[\frac{2\theta^2L^5}{m^3(\theta\mu-1)}\Big(\frac1\mu+\frac\theta m\Big)+\frac C{m^2}\Big],\quad C_5=\frac2{1-\rho_w^2}\Big[\frac{2\theta^3L^3}{m^2(\theta\mu-1)}+\frac{3\theta^2L^2}{m^2}+2\Big(\frac{\theta L}m+1\Big)(n+1)\Big]\sigma^2,$$
--   $$\hat X=\max\Big\{\frac{C_3}{C_1-C_2},\frac{C_5}{C_1-C_4},m^2X_0,\frac{Y_0}{C_1}\Big\},\qquad \hat U=\max\Big\{\frac1{n(\theta\mu-1)}\Big[\Big(\frac{\theta L^2}{\mu m}+\frac{\theta^2L^2}{m^2}\Big)\hat X+\theta^2\sigma^2\Big],\;m\|\bar x_0-x^*\|^2\Big\}.$$
--   Then the three errors are expectations of integrable random variables, and there is $\hat Y$ such that for every $k\ge0$
--   $$U_k\le\frac{\hat U}{m+k},\qquad X_k\le\frac{\hat X}{(m+k)^2},\qquad Y_k\le\hat Y.$$
--
--   This is the first half of the proof of Theorem 2: it gives the rate $X_k=O(1/k^2)$ of (15b) and the bound on $X_k$ that feeds the refined recursion for $U_k$.
--
--   **Formalization Note** The hypothesis $3\theta L\le m$ is not on the page; it gives $\alpha_kL\le1/3$ for every $k$, which the linear system (29) needs (see `linear_system_k`). The page leaves $\hat Y$ implicit ("lower bounded under constraints (34b), (34c), $\hat Y\ge Y_0$"), so it is existential here. Condition (35) of the page is exactly the second line of (14).
-- source:
--   Pu & Nedić, Math. Program. 187 (2021), §3.3, (32)–(36), pp. 425–427

import Mathlib
import Definitions.Def_StochGradTrack_Dimin_Model
import Definitions.Def_StochGradTrack_Dimin_StepSystem

open MeasureTheory ProbabilityTheory

namespace StochGradTrack.Dimin

/-- The induction (32)–(36) (pp. 425–427): under the hypotheses of Theorem 2 and (disclosed) `3θL ≤ m`,
`U_k ≤ Û/(m+k)`, `X_k ≤ X̂/(m+k)²` and `Y_k ≤ Ŷ` for all `k`, with `Û`, `X̂` as printed on p. 426. -/
theorem induction_bounds
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
      > 1 / (θ * μ - 1) * (1 / μ + θ / m) * (4 * θ ^ 2 * L ^ 5 / m ^ 3) + 2 * Cconst θ m L ρ w / m ^ 2)
    (h3 : 3 * θ * L ≤ m) :
    let U : ℕ → ℝ := fun j => ∫ ω, ‖avg (xs (stepDimin θ m) W g ξ x0 j ω) - xstar‖ ^ 2 ∂P
    let X : ℕ → ℝ := fun j => ∫ ω, consErr (xs (stepDimin θ m) W g ξ x0 j ω) ∂P
    let Y : ℕ → ℝ := fun j => ∫ ω, consErr (ys (stepDimin θ m) W g ξ x0 j ω) ∂P
    let C := Cconst θ m L ρ w
    let X₀ := consErr x0
    let Y₀ := Y 0
    let D₀ := ‖avg x0 - xstar‖ ^ 2
    let C₁ := (1 - ρ ^ 2) / (θ ^ 2 * (1 + ρ ^ 2) * ρ ^ 2) * ((1 - ρ ^ 2) / 2 - (2 * m + 1) / (m + 1) ^ 2)
    let C₂ := 2 * C / ((1 - ρ ^ 2) * m ^ 2)
    let C₃ := 2 / (1 - ρ ^ 2) * (2 * θ * n * L ^ 3 * D₀ / m
      + (3 * θ ^ 2 * L ^ 2 / m ^ 2 + 2 * (θ * L / m + 1) * (n + 1)) * σ ^ 2)
    let C₄ := 2 / (1 - ρ ^ 2) * (2 * θ ^ 2 * L ^ 5 / (m ^ 3 * (θ * μ - 1)) * (1 / μ + θ / m) + C / m ^ 2)
    let C₅ := 2 / (1 - ρ ^ 2) * (2 * θ ^ 3 * L ^ 3 / (m ^ 2 * (θ * μ - 1)) + 3 * θ ^ 2 * L ^ 2 / m ^ 2
      + 2 * (θ * L / m + 1) * (n + 1)) * σ ^ 2
    let Xhat := max (max (C₃ / (C₁ - C₂)) (C₅ / (C₁ - C₄))) (max (m ^ 2 * X₀) (Y₀ / C₁))
    let Uhat := max (1 / (n * (θ * μ - 1)) * ((θ * L ^ 2 / (μ * m) + θ ^ 2 * L ^ 2 / m ^ 2) * Xhat
      + θ ^ 2 * σ ^ 2)) (m * D₀)
    (∀ j : ℕ, Integrable (fun ω => ‖avg (xs (stepDimin θ m) W g ξ x0 j ω) - xstar‖ ^ 2) P ∧
      Integrable (fun ω => consErr (xs (stepDimin θ m) W g ξ x0 j ω)) P ∧
      Integrable (fun ω => consErr (ys (stepDimin θ m) W g ξ x0 j ω)) P) ∧
    ∃ Yhat : ℝ, ∀ k : ℕ, U k ≤ Uhat / (m + k) ∧ X k ≤ Xhat / (m + k) ^ 2 ∧ Y k ≤ Yhat := by sorry

end StochGradTrack.Dimin
