-- Prove2me | Theorems.Thm_StochModelWC_ProjSubgrad_theorem_3_1
-- name    : StochModelWC.ProjSubgrad.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:35:06.854347+00:00
-- url     : https://prove2.me/theorems/4ce59471-4464-46cf-bf65-437d0c02e9c9
-- title:
--   Theorem 3.1 — the projected stochastic subgradient method drives E‖∇φ_{1/ρ̄}(x_{t*})‖² to zero, (3.4) and (3.5)
-- statement:
--   Let $X \subseteq \mathbb R^d$ be nonempty, closed and convex, let $f : \mathbb R^d \to \mathbb R$ be $\rho$-weakly convex with $\rho > 0$, and let $\varphi = f + \delta_X$, so that $\min \varphi = \inf_{X} f$. Suppose Assumption A holds with $D = X$ (stochastic subgradients $G$ of $f$ on an open $U \supseteq X$ with second moment at most $L^2$ on $X$). Run the projected stochastic subgradient method (Algorithm 3.1 with $r = \delta_X$)
--   $$x_{t+1} = \operatorname{proj}_X\big(x_t - \alpha_t G(x_t, \xi_t)\big), \qquad t = 0, \dots, T,$$
--   from $x_0 \in X$ with i.i.d. samples $\xi_0, \dots, \xi_T \sim P$ and stepsizes $\alpha_t \ge 0$, and return $x_{t^*}$ with $t^*$ drawn independently with $P(t^* = t) = \alpha_t / \sum_{i=0}^T \alpha_i$. Let $\varphi^*$ be any lower bound of $f$ on $X$ (for instance $\min\varphi$). Then:
--
--   1. if $\sum_{t=0}^T \alpha_t > 0$, for every $\bar\rho > \rho$,
--   $$\mathbb E\big[\|\nabla\varphi_{1/\bar\rho}(x_{t^*})\|^2\big] \le \frac{\bar\rho}{\bar\rho - \rho}\cdot\frac{\big(\varphi_{1/\bar\rho}(x_0) - \varphi^*\big) + \frac{\bar\rho L^2}{2}\sum_{t=0}^T \alpha_t^2}{\sum_{t=0}^T \alpha_t}; \tag{3.4}$$
--   2. if $\alpha_t = \gamma/\sqrt{T+1}$ for all $t$, with $\gamma > 0$,
--   $$\mathbb E\big[\|\nabla\varphi_{1/(2\rho)}(x_{t^*})\|^2\big] \le 2\cdot\frac{\big(\varphi_{1/(2\rho)}(x_0) - \varphi^*\big) + \rho L^2\gamma^2}{\gamma\sqrt{T+1}}. \tag{3.5}$$
--
--   Here $\varphi_{\lambda}(x) = \min_{y \in X}\{f(y) + \frac{1}{2\lambda}\|y - x\|^2\}$ is the Moreau envelope, whose gradient norm measures near-stationarity: a small $\|\nabla\varphi_\lambda(x)\|$ means that $x$ is close to a point that is nearly stationary for the constrained problem $\min_{x \in X} f(x)$. The bound (3.5) gives the rate $O(1/\sqrt{T})$ for nonsmooth nonconvex (weakly convex) constrained stochastic optimization, with no restriction on the stepsizes beyond nonnegativity.
--
--   **Formalization Note.** The expectation is over the product measure $P^{\otimes(T+1)}$ on sample paths; since $t^*$ is drawn independently of the samples, $\mathbb E\|\nabla\varphi_{1/\bar\rho}(x_{t^*})\|^2$ is written as the $\alpha$-weighted average $\sum_t \alpha_t\,\mathbb E\|\nabla\varphi_{1/\bar\rho}(x_t)\|^2 / \sum_t \alpha_t$, exactly as the paper's proof identifies it. Each conclusion also asserts integrability of the integrands. The positivity of $\sum_t \alpha_t$ (needed for $t^*$ to be well defined) and $\rho > 0$ (implicit in the envelope $\varphi_{1/(2\rho)}$ and in Lemma 2.2's interval $(0, \rho^{-1})$) are stated as hypotheses. $\min\varphi$ is replaced by an arbitrary lower bound $\varphi^*$ of $f$ on $X$, which is equivalent since the bound is monotone in $\varphi^*$.
-- source:
--   Davis–Drusvyatskiy, Stochastic Model-Based Minimization of Weakly Convex Functions, arXiv:1803.06523v3, p. 13, Theorem 3.1, (3.4) and (3.5)

import Mathlib
import Definitions.Def_StochModelWC_ProjSubgrad_Basic
import Definitions.Def_StochModelWC_ProxSubgrad_AssumptionA
import Definitions.Def_StochModelWC_ProjSubgrad_Algorithm31Proj
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto

open MeasureTheory Filter Topology

namespace StochModelWC.ProjSubgrad

/-- Theorem 3.1 (p. 13), (3.4) and (3.5). The output `x_{t*}` is drawn with `P(t* = t) = α_t / Σ α_i`,
independently of the samples, so `E‖∇φ_{1/ρ̄}(x_{t*})‖²` is the `α`-weighted average of
`E‖∇φ_{1/ρ̄}(x_t)‖²`, `t = 0, …, T`. `phiStar` is any lower bound of `f` on `X` (e.g. `min φ`). The stepsizes
`α_t ≥ 0` are otherwise unrestricted. -/
theorem theorem_3_1 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U X : Set (EuclideanSpace ℝ (Fin d))) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (G : EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d)) (ρ L : ℝ)
    (hX_cl : IsClosed X) (hX_cvx : Convex ℝ X) (hX_ne : X.Nonempty)
    (hf : IsWeaklyConvexOn Set.univ ρ f) (hρ : 0 < ρ) (hA : StochModelWC.ProxSubgrad.AssumptionA P U X f G L)
    (proj : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hproj : SpectralProjGrad.Shared.IsProjOnto X proj)
    (x0 : EuclideanSpace ℝ (Fin d)) (hx0 : x0 ∈ X) (T : ℕ) (α : ℕ → ℝ)
    (hα : ∀ t ≤ T, 0 ≤ α t)
    (phiStar : ℝ) (hphiStar : ∀ y ∈ X, phiStar ≤ f y) :
    -- (3.4)
    (0 < ∑ t ∈ Finset.range (T + 1), α t → ∀ ρbar : ℝ, ρ < ρbar →
      (∀ t ≤ T, Integrable (fun ω => ‖gradient (moreauEnv X f (1 / ρbar))
          (projSGIter proj G α x0 ω t)‖ ^ 2) (Measure.pi (fun _ : Fin (T + 1) => P))) ∧
      (∑ t ∈ Finset.range (T + 1), α t *
          ∫ ω, ‖gradient (moreauEnv X f (1 / ρbar))
            (projSGIter proj G α x0 ω t)‖ ^ 2 ∂(Measure.pi (fun _ : Fin (T + 1) => P))) /
          (∑ t ∈ Finset.range (T + 1), α t) ≤
        ρbar / (ρbar - ρ) *
          ((moreauEnv X f (1 / ρbar) x0 - phiStar) +
            ρbar * L ^ 2 / 2 * ∑ t ∈ Finset.range (T + 1), α t ^ 2) /
          (∑ t ∈ Finset.range (T + 1), α t)) ∧
    -- (3.5)
    (∀ γ : ℝ, 0 < γ → (∀ t ≤ T, α t = γ / Real.sqrt ((T : ℝ) + 1)) →
      (∀ t ≤ T, Integrable (fun ω => ‖gradient (moreauEnv X f (1 / (2 * ρ)))
          (projSGIter proj G α x0 ω t)‖ ^ 2) (Measure.pi (fun _ : Fin (T + 1) => P))) ∧
      (∑ t ∈ Finset.range (T + 1), α t *
          ∫ ω, ‖gradient (moreauEnv X f (1 / (2 * ρ)))
            (projSGIter proj G α x0 ω t)‖ ^ 2 ∂(Measure.pi (fun _ : Fin (T + 1) => P))) /
          (∑ t ∈ Finset.range (T + 1), α t) ≤
        2 * ((moreauEnv X f (1 / (2 * ρ)) x0 - phiStar) + ρ * L ^ 2 * γ ^ 2) /
          (γ * Real.sqrt ((T : ℝ) + 1))) := by sorry

end StochModelWC.ProjSubgrad
