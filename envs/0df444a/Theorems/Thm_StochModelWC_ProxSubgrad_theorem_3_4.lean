-- Prove2me | Theorems.Thm_StochModelWC_ProxSubgrad_theorem_3_4
-- name    : StochModelWC.ProxSubgrad.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:47:01.149514+00:00
-- url     : https://prove2.me/theorems/9eaecb0d-3540-4e55-8458-7b38a06f4f24
-- title:
--   Theorem 3.4 — the proximal stochastic subgradient method: E‖∇φ_{1/ρ̄}(x_{t*})‖² bounds (3.15) and (3.16)
-- statement:
--   Consider $\min_x \varphi(x) = f(x) + r(x)$, where $r : \mathbb R^d \to \mathbb R \cup \{+\infty\}$ is closed and convex with nonempty domain $D$, $f : \mathbb R^d \to \mathbb R$ is $\rho$-weakly convex, and $f$ is accessed through a stochastic subgradient oracle $G$ satisfying Assumption A with constant $L$. Run Algorithm 3.1 from $x_0 \in D$ with stepsizes $\alpha_0, \dots, \alpha_T$ on i.i.d. samples $\xi_0, \dots, \xi_T \sim P$, and let $t^* \in \{0, \dots, T\}$ be drawn independently with $P(t^* = t) = \alpha_t / \sum_{i=0}^T \alpha_i$. Let $\varphi^*$ be a lower bound of $\varphi$ (for instance $\min\varphi$).
--
--   1. If $\bar\rho \in (\rho, 2\rho]$ and $\alpha_t \in (0, 1/\bar\rho]$ for all $t \le T$, then
--   $$\mathbb E\big[\|\nabla\varphi_{1/\bar\rho}(x_{t^*})\|^2\big] \le \frac{\bar\rho}{\bar\rho - \rho}\cdot\frac{\big(\varphi_{1/\bar\rho}(x_0) - \varphi^*\big) + 2\bar\rho L^2\sum_{t=0}^T\alpha_t^2}{\sum_{t=0}^T\alpha_t}. \tag{3.15}$$
--   2. If $\alpha_t = \gamma/\sqrt{T+1}$ for all $t \le T$, with $\gamma \in (0, \frac{1}{2\rho}]$, then
--   $$\mathbb E\big[\|\nabla\varphi_{1/(2\rho)}(x_{t^*})\|^2\big] \le 2\cdot\frac{\big(\varphi_{1/(2\rho)}(x_0) - \varphi^*\big) + 4\rho L^2\gamma^2}{\gamma\sqrt{T+1}}. \tag{3.16}$$
--
--   In both cases the random variables $\|\nabla\varphi_{1/\bar\rho}(x_t)\|^2$ are integrable. Since $\|\nabla\varphi_{1/\bar\rho}(x)\|$ controls the distance from $x$ to a nearly stationary point of $\varphi$, (3.16) shows that $\mathbb E\|\nabla\varphi_{1/(2\rho)}(x_{t^*})\|^2$ decays at the rate $O(1/\sqrt{T})$.
--
--   **Formalization Note.** $\mathbb E$ is the integral against the product measure $P^{\otimes(T+1)}$ on sample paths. Because $t^*$ is independent of the samples, $\mathbb E[\|\nabla\varphi_{1/\bar\rho}(x_{t^*})\|^2]$ is written as the $\alpha$-weighted average $\sum_t \alpha_t\,\mathbb E\|\nabla\varphi_{1/\bar\rho}(x_t)\|^2 / \sum_t \alpha_t$, exactly as the paper's proof identifies it ((3.17)). $\min\varphi$ is replaced by an arbitrary real lower bound $\varphi^*$ of $\varphi$ on $D$, which is equivalent since the bound is monotone in $\varphi^*$. The proximal map is a function `prox` constrained to return a proximal point of $a r$ for every $a > 0$.
-- source:
--   Davis–Drusvyatskiy, Stochastic Model-Based Minimization of Weakly Convex Functions, arXiv:1803.06523v3, p. 16, Theorem 3.4, (3.15) and (3.16) (proof pp. 16–17)

import Mathlib
import Definitions.Def_StochModelWC_ProxSubgrad_Basic
import Definitions.Def_StochModelWC_ProxSubgrad_AssumptionA
import Definitions.Def_StochModelWC_ProxSubgrad_Algorithm31

open MeasureTheory Filter Topology

namespace StochModelWC.ProxSubgrad

/-- Theorem 3.4 (p. 16), (3.15) and (3.16). The output `x_{t*}` is drawn with `P(t* = t) = α_t / Σ α_i`,
independently of the samples, so `E‖∇φ_{1/ρ̄}(x_{t*})‖²` is the `α`-weighted average of
`E‖∇φ_{1/ρ̄}(x_t)‖²`, `t = 0, …, T`. `phiStar` is any lower bound of `φ = f + r` on `dom r` (e.g. `min φ`). -/
theorem theorem_3_4 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U D : Set (EuclideanSpace ℝ (Fin d))) (f r : EuclideanSpace ℝ (Fin d) → ℝ)
    (G : EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d)) (ρ L : ℝ)
    (hD : D.Nonempty) (hr_cl : StochModelWC.ModelBased.IsClosedFn D r) (hr_cvx : ConvexOn ℝ D r)
    (hf : StochModelWC.ModelBased.IsWeaklyConvexOn Set.univ ρ f) (hA : AssumptionA P U D f G L)
    (prox : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hprox : ∀ a : ℝ, 0 < a → ∀ z, StochModelWC.ModelBased.IsProxPt D r a z (prox a z))
    (x0 : EuclideanSpace ℝ (Fin d)) (hx0 : x0 ∈ D) (T : ℕ) (α : ℕ → ℝ)
    (phiStar : ℝ) (hphiStar : ∀ y ∈ D, phiStar ≤ f y + r y) :
    -- (3.15)
    (∀ ρbar : ℝ, ρ < ρbar → ρbar ≤ 2 * ρ → (∀ t ≤ T, 0 < α t ∧ α t ≤ 1 / ρbar) →
      (∀ t ≤ T, Integrable (fun ω => ‖gradient (StochModelWC.ModelBased.moreauEnv D (fun y => f y + r y) (1 / ρbar))
          (proxSGIter prox G α x0 ω t)‖ ^ 2) (Measure.pi (fun _ : Fin (T + 1) => P))) ∧
      (∑ t ∈ Finset.range (T + 1), α t *
          ∫ ω, ‖gradient (StochModelWC.ModelBased.moreauEnv D (fun y => f y + r y) (1 / ρbar))
            (proxSGIter prox G α x0 ω t)‖ ^ 2 ∂(Measure.pi (fun _ : Fin (T + 1) => P))) /
          (∑ t ∈ Finset.range (T + 1), α t) ≤
        ρbar / (ρbar - ρ) *
          ((StochModelWC.ModelBased.moreauEnv D (fun y => f y + r y) (1 / ρbar) x0 - phiStar) +
            2 * ρbar * L ^ 2 * ∑ t ∈ Finset.range (T + 1), α t ^ 2) /
          (∑ t ∈ Finset.range (T + 1), α t)) ∧
    -- (3.16)
    (∀ γ : ℝ, 0 < γ → γ ≤ 1 / (2 * ρ) → (∀ t ≤ T, α t = γ / Real.sqrt ((T : ℝ) + 1)) →
      (∀ t ≤ T, Integrable (fun ω => ‖gradient (StochModelWC.ModelBased.moreauEnv D (fun y => f y + r y) (1 / (2 * ρ)))
          (proxSGIter prox G α x0 ω t)‖ ^ 2) (Measure.pi (fun _ : Fin (T + 1) => P))) ∧
      (∑ t ∈ Finset.range (T + 1), α t *
          ∫ ω, ‖gradient (StochModelWC.ModelBased.moreauEnv D (fun y => f y + r y) (1 / (2 * ρ)))
            (proxSGIter prox G α x0 ω t)‖ ^ 2 ∂(Measure.pi (fun _ : Fin (T + 1) => P))) /
          (∑ t ∈ Finset.range (T + 1), α t) ≤
        2 * ((StochModelWC.ModelBased.moreauEnv D (fun y => f y + r y) (1 / (2 * ρ)) x0 - phiStar) + 4 * ρ * L ^ 2 * γ ^ 2) /
          (γ * Real.sqrt ((T : ℝ) + 1))) := by sorry

end StochModelWC.ProxSubgrad
