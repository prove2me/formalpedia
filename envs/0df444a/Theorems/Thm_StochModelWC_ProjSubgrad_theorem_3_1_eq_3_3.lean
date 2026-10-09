-- Prove2me | Theorems.Thm_StochModelWC_ProjSubgrad_theorem_3_1_eq_3_3
-- name    : StochModelWC.ProjSubgrad.theorem_3_1_eq_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:35:35.007526+00:00
-- url     : https://prove2.me/theorems/3453d3d2-a454-4b92-a68f-b3315d208f9f
-- title:
--   Theorem 3.1, (3.3) — expected descent of φ_{1/ρ̄} along the projected stochastic subgradient method
-- statement:
--   Let $X \subseteq \mathbb R^d$ be nonempty, closed and convex, let $f : \mathbb R^d \to \mathbb R$ be $\rho$-weakly convex with $\rho > 0$, and let $\varphi = f + \delta_X$. Suppose Assumption A holds with $D = X$: an open $U \supseteq X$ and a measurable stochastic subgradient $G$ with $\mathbb E_\xi[G(x,\xi)] \in \partial f(x)$ for $x \in U$ and $\mathbb E_\xi\|G(x,\xi)\|^2 \le L^2$ for $x \in X$. Run the projected stochastic subgradient method
--   $$x_{t+1} = \operatorname{proj}_X\big(x_t - \alpha_t G(x_t, \xi_t)\big), \qquad t = 0, \dots, T,$$
--   from $x_0 \in X$ with i.i.d. samples $\xi_0, \dots, \xi_T \sim P$ and arbitrary stepsizes $\alpha_t \ge 0$. Then for every $\bar\rho > \rho$ and every $t \in \{0, \dots, T\}$,
--   $$\mathbb E\big[\varphi_{1/\bar\rho}(x_{t+1})\big] \le \mathbb E\big[\varphi_{1/\bar\rho}(x_t)\big] - \frac{\alpha_t(\bar\rho - \rho)}{\bar\rho}\,\mathbb E\big[\|\nabla\varphi_{1/\bar\rho}(x_t)\|^2\big] + \frac{\alpha_t^2\bar\rho L^2}{2},$$
--   and the three expectations are finite. Here $\varphi_{1/\bar\rho}(x) = \min_{y \in X}\{f(y) + \frac{\bar\rho}{2}\|y - x\|^2\}$.
--
--   This is the one-step estimate of Theorem 3.1: the Moreau envelope is an approximate Lyapunov function for the method, decreasing in expectation by an amount proportional to the stationarity measure up to an $O(\alpha_t^2)$ error. No restriction on the stepsizes is needed.
--
--   **Formalization Note.** The expectation is over the product measure $P^{\otimes(T+1)}$ on sample paths $(\xi_0, \dots, \xi_T)$. The projection is a function `proj` constrained to return a nearest point of $X$ (`SpectralProjGrad.Shared.IsProjOnto X proj`). The conclusion also asserts integrability of each integrand, since a Bochner integral of a non-integrable function is $0$ in Lean.
-- source:
--   Davis–Drusvyatskiy, Stochastic Model-Based Minimization of Weakly Convex Functions, arXiv:1803.06523v3, p. 13, Theorem 3.1, (3.3)

import Mathlib
import Definitions.Def_StochModelWC_ProjSubgrad_Basic
import Definitions.Def_StochModelWC_ProxSubgrad_AssumptionA
import Definitions.Def_StochModelWC_ProjSubgrad_Algorithm31Proj
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto

open MeasureTheory Filter Topology

namespace StochModelWC.ProjSubgrad

/-- Theorem 3.1, (3.3) (p. 13): along the projected stochastic subgradient method (Algorithm 3.1 with
`r = δ_X`) run on `T + 1` i.i.d. samples with any stepsizes `α_t ≥ 0`, for every `ρ̄ > ρ` and every `t ≤ T`,
`E[φ_{1/ρ̄}(x_{t+1})] ≤ E[φ_{1/ρ̄}(x_t)] − α_t(ρ̄ − ρ)/ρ̄ · E‖∇φ_{1/ρ̄}(x_t)‖² + α_t² ρ̄ L²/2`,
where `φ_{1/ρ̄}` is the Moreau envelope of `φ = f + δ_X`. -/
theorem theorem_3_1_eq_3_3 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (U X : Set (EuclideanSpace ℝ (Fin d))) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (G : EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d)) (ρ L : ℝ)
    (hX_cl : IsClosed X) (hX_cvx : Convex ℝ X) (hX_ne : X.Nonempty)
    (hf : IsWeaklyConvexOn Set.univ ρ f) (hρ : 0 < ρ) (hA : StochModelWC.ProxSubgrad.AssumptionA P U X f G L)
    (proj : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hproj : SpectralProjGrad.Shared.IsProjOnto X proj)
    (x0 : EuclideanSpace ℝ (Fin d)) (hx0 : x0 ∈ X) (T : ℕ) (α : ℕ → ℝ)
    (hα : ∀ t ≤ T, 0 ≤ α t) (ρbar : ℝ) (hρbar : ρ < ρbar) :
    ∀ t ≤ T,
      Integrable (fun ω => moreauEnv X f (1 / ρbar) (projSGIter proj G α x0 ω (t + 1)))
        (Measure.pi (fun _ : Fin (T + 1) => P)) ∧
      Integrable (fun ω => moreauEnv X f (1 / ρbar) (projSGIter proj G α x0 ω t))
        (Measure.pi (fun _ : Fin (T + 1) => P)) ∧
      Integrable (fun ω => ‖gradient (moreauEnv X f (1 / ρbar)) (projSGIter proj G α x0 ω t)‖ ^ 2)
        (Measure.pi (fun _ : Fin (T + 1) => P)) ∧
      ∫ ω, moreauEnv X f (1 / ρbar) (projSGIter proj G α x0 ω (t + 1))
          ∂(Measure.pi (fun _ : Fin (T + 1) => P)) ≤
        ∫ ω, moreauEnv X f (1 / ρbar) (projSGIter proj G α x0 ω t)
          ∂(Measure.pi (fun _ : Fin (T + 1) => P))
        - α t * (ρbar - ρ) / ρbar *
          ∫ ω, ‖gradient (moreauEnv X f (1 / ρbar)) (projSGIter proj G α x0 ω t)‖ ^ 2
            ∂(Measure.pi (fun _ : Fin (T + 1) => P))
        + α t ^ 2 * ρbar * L ^ 2 / 2 := by sorry

end StochModelWC.ProjSubgrad
