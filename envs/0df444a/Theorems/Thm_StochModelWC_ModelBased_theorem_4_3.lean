-- Prove2me | Theorems.Thm_StochModelWC_ModelBased_theorem_4_3
-- name    : StochModelWC.ModelBased.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:52:03.44833+00:00
-- url     : https://prove2.me/theorems/d5cd462c-62ed-4f26-a2c4-40d2f6e0d9e4
-- title:
--   Theorem 4.3, (4.15)–(4.16) — stochastic model-based minimization drives E‖∇φ_{1/ρ̄}(x_{t*})‖² to zero at rate O(1/√T)
-- statement:
--   Consider $\min_x\varphi(x)=f(x)+r(x)$, where $r:\mathbb R^d\to\mathbb R\cup\{\infty\}$ is closed and proper with domain $D$ and $f:\mathbb R^d\to\mathbb R$ is locally Lipschitz, and suppose Assumption B holds with constants $\tau$, $\eta$, $\mathsf L$ for a stochastic one-sided model $f_x(y,\xi)$ on an open convex $U\supseteq D$. Let $\varphi^*$ be a lower bound of $\varphi$ on $D$ (e.g. $\min_x\varphi$). Fix a real $\bar\rho>\tau+\eta$ with $\bar\rho>0$ and a sequence $(\beta_t)$ with $\beta_t>\bar\rho$ and $\beta_t>\eta$. Run Algorithm 4.1 from $x_0\in U$ on i.i.d. samples $\xi_0,\dots,\xi_T\sim P$, and draw $t^*\in\{0,\dots,T\}$ independently with $\mathbb P(t^*=t)\propto\frac{\bar\rho-\tau-\eta}{\beta_t-\eta}$. Then
--
--   1. each $\|\nabla\varphi_{1/\bar\rho}(x_t)\|^2$, $t\le T$, is integrable;
--   2. the returned point satisfies
--   $$\mathbb E\|\nabla\varphi_{1/\bar\rho}(x_{t^*})\|^2\le\frac{\bar\rho\big(\varphi_{1/\bar\rho}(x_0)-\varphi^*\big)+2\bar\rho^2\mathsf L^2\sum_{t=0}^T\frac{1}{(\beta_t-\eta)(\beta_t-\bar\rho)}}{\sum_{t=0}^T\frac{\bar\rho-\tau-\eta}{2(\beta_t-\eta)}}; \tag{4.15}$$
--   3. if $\eta\le\bar\rho$ and $\beta_t=\bar\rho+\gamma^{-1}\sqrt{T+1}$ for $t=0,\dots,T$ and some real $\gamma>0$, then
--   $$\mathbb E\|\nabla\varphi_{1/\bar\rho}(x_{t^*})\|^2\le\frac{2\big(\bar\rho(\varphi_{1/\bar\rho}(x_0)-\varphi^*)+2\bar\rho^2\mathsf L^2\gamma^2\big)}{\bar\rho-\tau-\eta}\cdot\Big(\frac{\bar\rho-\eta}{T+1}+\frac{1}{\gamma\sqrt{T+1}}\Big). \tag{4.16}$$
--
--   Since $\|\nabla\varphi_{1/\bar\rho}(x)\|$ measures near-stationarity (a small value means $x$ is close to a point that is nearly stationary for $\varphi$), this gives an $O(\varepsilon^{-4})$ sample complexity for the stochastic proximal point, prox-linear and proximal subgradient methods on weakly convex problems.
--
--   **Formalization Note** The samples are a point of $\Omega^{T+1}$ under the product measure, and $\mathbb E\|\nabla\varphi_{1/\bar\rho}(x_{t^*})\|^2$ is written as the weighted average $\sum_t w_t\,\mathbb E\|\nabla\varphi_{1/\bar\rho}(x_t)\|^2/\sum_t w_t$ with $w_t=\frac{\bar\rho-\tau-\eta}{\beta_t-\eta}$, which is exactly its value when $t^*$ is drawn independently of the samples. The update is any measurable selection of the argmin of Algorithm 4.1. The paper's statement says "Algorithm 3.1" twice; both mean Algorithm 4.1 (only it has the parameters $\beta_t$). $\beta_t>\eta$, $\bar\rho>0$ and $x_0\in U$ are implicit in the paper: Assumption B allows any real $\tau$, and when $\tau<0$ the paper's $\beta_t>\bar\rho>\tau+\eta$ does not give the $\beta_t>\eta$ its proof uses. (4.16) is stated with the paper's constant, which follows from (4.15) when $\eta\le\bar\rho$ (the printed bound exceeds the (4.15) value by a multiple of $\bar\rho-\eta$); that condition, automatic when $\tau\ge0$, is therefore part of (4.16) here.
-- source:
--   Davis–Drusvyatskiy, Stochastic Model-Based Minimization of Weakly Convex Functions, arXiv:1803.06523v3, p. 21, Theorem 4.3, (4.15)–(4.16); p. 19, Algorithm 4.1

import Mathlib
import Definitions.Def_StochModelWC_ModelBased_Basic
import Definitions.Def_StochModelWC_ModelBased_AssumptionB

open MeasureTheory Filter Topology

namespace StochModelWC.ModelBased

/-- Theorem 4.3, (4.15) and (4.16) (p. 21): the point `x_{t*}` returned by Algorithm 4.1, with
`P(t* = t) ∝ (ρ̄ − τ − η)/(β_t − η)` drawn independently of the samples, satisfies the stated bounds on
`E‖∇φ_{1/ρ̄}(x_{t*})‖²`, written as the weighted average of `E‖∇φ_{1/ρ̄}(x_t)‖²`, `t = 0, …, T`. `phiStar` is any
lower bound of `φ = f + r` on `dom r` (the paper's `min_x φ`). -/
theorem theorem_4_3 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U D : Set (EuclideanSpace ℝ (Fin d))) (f r : EuclideanSpace ℝ (Fin d) → ℝ)
    (model : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (τ η L : ℝ) (Lfun : Ω → ℝ)
    (hD : D.Nonempty) (hr : IsClosedFn D r) (hf : LocallyLipschitz f)
    (hB : AssumptionB P U D f r model τ η L Lfun)
    (ρbar : ℝ) (hρbar : τ + η < ρbar) (hρbar0 : 0 < ρbar)
    (β : ℕ → ℝ) (hβ : ∀ t, ρbar < β t) (hβη : ∀ t, η < β t)
    (upd : ℕ → EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d))
    (hupd : IsAlg41Step P U D r model β upd)
    (x0 : EuclideanSpace ℝ (Fin d)) (hx0 : x0 ∈ U) (T : ℕ)
    (phiStar : ℝ) (hphiStar : ∀ y ∈ D, phiStar ≤ f y + r y) :
    (∀ t ≤ T, Integrable (fun ω : Fin (T + 1) → Ω =>
        ‖gradient (moreauEnv D (fun y => f y + r y) (1 / ρbar)) (run upd x0 ω t)‖ ^ 2)
        (Measure.pi fun _ : Fin (T + 1) => P)) ∧
    -- (4.15)
    (∑ t ∈ Finset.range (T + 1), (ρbar - τ - η) / (β t - η) *
        ∫ ω, ‖gradient (moreauEnv D (fun y => f y + r y) (1 / ρbar)) (run upd x0 ω t)‖ ^ 2
          ∂(Measure.pi fun _ : Fin (T + 1) => P)) /
      (∑ t ∈ Finset.range (T + 1), (ρbar - τ - η) / (β t - η)) ≤
      (ρbar * (moreauEnv D (fun y => f y + r y) (1 / ρbar) x0 - phiStar)
          + 2 * ρbar ^ 2 * L ^ 2 * ∑ t ∈ Finset.range (T + 1), 1 / ((β t - η) * (β t - ρbar))) /
        ∑ t ∈ Finset.range (T + 1), (ρbar - τ - η) / (2 * (β t - η)) ∧
    -- (4.16)
    ∀ γ : ℝ, 0 < γ → η ≤ ρbar → (∀ t ≤ T, β t = ρbar + γ⁻¹ * Real.sqrt ((T : ℝ) + 1)) →
      (∑ t ∈ Finset.range (T + 1), (ρbar - τ - η) / (β t - η) *
          ∫ ω, ‖gradient (moreauEnv D (fun y => f y + r y) (1 / ρbar)) (run upd x0 ω t)‖ ^ 2
            ∂(Measure.pi fun _ : Fin (T + 1) => P)) /
        (∑ t ∈ Finset.range (T + 1), (ρbar - τ - η) / (β t - η)) ≤
        2 * (ρbar * (moreauEnv D (fun y => f y + r y) (1 / ρbar) x0 - phiStar)
            + 2 * ρbar ^ 2 * L ^ 2 * γ ^ 2) / (ρbar - τ - η) *
          ((ρbar - η) / ((T : ℝ) + 1) + 1 / (γ * Real.sqrt ((T : ℝ) + 1))) := by sorry

end StochModelWC.ModelBased
