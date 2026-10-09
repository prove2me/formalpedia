-- Prove2me | Theorems.Thm_StochModelWC_Convex_theorem_4_1
-- name    : StochModelWC.Convex.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:41:55.072402+00:00
-- url     : https://prove2.me/theorems/ec99e235-d06d-4f04-b81e-736b6dc4d645
-- title:
--   Theorem 4.1 — under convexity, E[φ(x̄_T) − φ(x*)] ≤ (½‖x₀−x*‖² + 2𝖫²Σα_t²)/Σα_t
-- statement:
--   **Setting.** Minimize $\varphi=f+r$ over $\mathbb R^d$, where $r:\mathbb R^d\to\mathbb R\cup\{\infty\}$ is closed with nonempty domain $D$ and $f$ is locally Lipschitz. Suppose Assumption B holds with $\tau=0$ and with the functions $f_x(\cdot,\xi)+r(\cdot)$ convex ($\eta=0$): stochastic models $f_x(\cdot,\xi)$, exact in expectation at the base point and lower-bounding $f$ in expectation, with a random Lipschitz constant $L(\xi)$ satisfying $\sqrt{\mathbb E L(\xi)^2}\le\mathsf L$. Run Algorithm 4.1 from $x_0\in U$,
--   $$x_{t+1}=\operatorname*{argmin}_{x}\Big\{r(x)+f_{x_t}(x,\xi_t)+\frac{1}{2\alpha_t}\|x-x_t\|^2\Big\},\qquad t=0,\dots,T,$$
--   with $\alpha_t>0$ (i.e. $\beta_t=\alpha_t^{-1}$) and i.i.d. samples $\xi_t\sim P$. Let $x^*$ be any minimizer of $\varphi$.
--
--   **Conclusion.** For every $T>0$,
--   $$\mathbb E\Big[\varphi\Big(\frac{1}{\sum_{t=0}^T\alpha_t}\sum_{t=0}^T\alpha_t x_{t+1}\Big)-\varphi(x^*)\Big]\le\frac{\frac12\|x_0-x^*\|^2+2\mathsf L^2\sum_{t=0}^T\alpha_t^2}{\sum_{t=0}^T\alpha_t}, \tag{4.17}$$
--   and if $\alpha_t=\gamma/\sqrt{T+1}$ for $t=0,\dots,T$ and some $\gamma>0$, then
--   $$\mathbb E\Big[\varphi\Big(\frac{1}{T+1}\sum_{t=1}^{T+1}x_t\Big)-\varphi(x^*)\Big]\le\frac{\frac12\|x_0-x^*\|^2+2\mathsf L^2\gamma^2}{\gamma\sqrt{T+1}}. \tag{4.18}$$
--   In both cases the function inside the expectation is integrable.
--
--   The theorem gives the $O(1/\sqrt T)$ function-gap rate for stochastic model-based minimization (stochastic proximal point, prox-linear and proximal subgradient methods) in the convex setting, with a bound in which no subgradient norm of $r$ appears.
--
--   **Formalization Note** The paper prints $\mathsf L^2$ in place of $2\mathsf L^2$ in (4.17) and (4.18). Its proof sums the first display of the proof (p. 23), which comes from (4.8); the proof of (4.8) yields the constant $4\mathsf L^2/(\beta_t(\beta_t-\eta))$, not the printed $2\mathsf L^2/(\beta_t(\beta_t-\eta))$, and this doubles the $\mathsf L^2$ term. The statement is what the proof establishes. Both averages lie in $D$ (a convex combination of points of the convex set $D$), so $\varphi$ is evaluated at points of its domain. Expectations are integrals against $P^{\otimes(T+1)}$; the minimizer $x^*$ is a point of $D$ with $\varphi(x^*)\le\varphi(y)$ for all $y\in D$. The paper's ρ̄ of Algorithm 4.1 does not affect the iterates; requiring $\beta_t>\bar\rho>0$ for the finitely many steps used is the same as $\alpha_t>0$. "Algorithm 3.1" before (4.18) is read as Algorithm 4.1. The constant $\mathsf L$ is `L` in Lean and $L(\xi)$ is `Lfun`.
-- source:
--   Davis–Drusvyatskiy, Stochastic Model-Based Minimization of Weakly Convex Functions, arXiv:1803.06523v3, p. 22, Theorem 4.1, (4.17)–(4.18); proof on p. 23; p. 19, Algorithm 4.1

import Mathlib
import Definitions.Def_StochModelWC_ModelBased_Basic
import Definitions.Def_StochModelWC_ModelBased_AssumptionB

open MeasureTheory Filter Topology

namespace StochModelWC.Convex

/-- Theorem 4.1 (p. 22), (4.17) and (4.18): in the convex setting (`τ = 0`, `f_x(·, ξ) + r` convex, i.e. `η = 0`),
Algorithm 4.1 with `β_t = α_t⁻¹`, StochModelWC.ModelBased.run on `T + 1` i.i.d. samples `ω = (ξ₀, …, ξ_T) ∼ P^{⊗(T+1)}`, satisfies, for any
minimizer `x*` of `φ = f + r`,
`E[φ(x̄_T) − φ(x*)] ≤ (½‖x₀ − x*‖² + 2 L² Σ_{t ≤ T} α_t²) / Σ_{t ≤ T} α_t`
for the `α`-weighted average `x̄_T` of `x_1, …, x_{T+1}`, and, for constant `α_t = γ/√(T+1)`,
`E[φ((T+1)⁻¹ Σ_{t=1}^{T+1} x_t) − φ(x*)] ≤ (½‖x₀ − x*‖² + 2 L² γ²) / (γ √(T+1))`.
The paper prints `L²` in place of `2 L²` in both bounds; its proof (via (4.8) as derived on p. 21) yields `2 L²`.
Both averages lie in `D = dom r`, so `φ` is evaluated at genuine points of its domain. -/
theorem theorem_4_1 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U D : Set (EuclideanSpace ℝ (Fin d))) (f r : EuclideanSpace ℝ (Fin d) → ℝ)
    (model : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (L : ℝ) (Lfun : Ω → ℝ)
    (hD : D.Nonempty) (hr : StochModelWC.ModelBased.IsClosedFn D r) (hf : LocallyLipschitz f)
    (hB : StochModelWC.ModelBased.AssumptionB P U D f r model 0 0 L Lfun)
    (α : ℕ → ℝ) (hα : ∀ t, 0 < α t)
    (upd : ℕ → EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d))
    (hupd : StochModelWC.ModelBased.IsAlg41Step P U D r model (fun t => (α t)⁻¹) upd)
    (x0 : EuclideanSpace ℝ (Fin d)) (hx0 : x0 ∈ U)
    (xstar : EuclideanSpace ℝ (Fin d)) (hxstar : xstar ∈ D)
    (hmin : ∀ y ∈ D, f xstar + r xstar ≤ f y + r y)
    (T : ℕ) (hT : 0 < T) :
    -- (4.17)
    (Integrable (fun ω : Fin (T + 1) → Ω =>
          f ((∑ t ∈ Finset.range (T + 1), α t)⁻¹ • ∑ t ∈ Finset.range (T + 1), α t • StochModelWC.ModelBased.run upd x0 ω (t + 1))
            + r ((∑ t ∈ Finset.range (T + 1), α t)⁻¹ •
                ∑ t ∈ Finset.range (T + 1), α t • StochModelWC.ModelBased.run upd x0 ω (t + 1)))
        (Measure.pi fun _ : Fin (T + 1) => P) ∧
      ∫ ω, (f ((∑ t ∈ Finset.range (T + 1), α t)⁻¹ •
                ∑ t ∈ Finset.range (T + 1), α t • StochModelWC.ModelBased.run upd x0 ω (t + 1))
            + r ((∑ t ∈ Finset.range (T + 1), α t)⁻¹ •
                ∑ t ∈ Finset.range (T + 1), α t • StochModelWC.ModelBased.run upd x0 ω (t + 1))
            - (f xstar + r xstar)) ∂(Measure.pi fun _ : Fin (T + 1) => P) ≤
        (1 / 2 * ‖x0 - xstar‖ ^ 2 + 2 * L ^ 2 * ∑ t ∈ Finset.range (T + 1), α t ^ 2) /
          ∑ t ∈ Finset.range (T + 1), α t) ∧
    -- (4.18)
    (∀ γ : ℝ, 0 < γ → (∀ t ≤ T, α t = γ / Real.sqrt ((T : ℝ) + 1)) →
      Integrable (fun ω : Fin (T + 1) → Ω =>
          f (((T : ℝ) + 1)⁻¹ • ∑ t ∈ Finset.Icc 1 (T + 1), StochModelWC.ModelBased.run upd x0 ω t)
            + r (((T : ℝ) + 1)⁻¹ • ∑ t ∈ Finset.Icc 1 (T + 1), StochModelWC.ModelBased.run upd x0 ω t))
        (Measure.pi fun _ : Fin (T + 1) => P) ∧
      ∫ ω, (f (((T : ℝ) + 1)⁻¹ • ∑ t ∈ Finset.Icc 1 (T + 1), StochModelWC.ModelBased.run upd x0 ω t)
            + r (((T : ℝ) + 1)⁻¹ • ∑ t ∈ Finset.Icc 1 (T + 1), StochModelWC.ModelBased.run upd x0 ω t)
            - (f xstar + r xstar)) ∂(Measure.pi fun _ : Fin (T + 1) => P) ≤
        (1 / 2 * ‖x0 - xstar‖ ^ 2 + 2 * L ^ 2 * γ ^ 2) / (γ * Real.sqrt ((T : ℝ) + 1))) := by sorry

end StochModelWC.Convex
