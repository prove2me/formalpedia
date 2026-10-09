-- Prove2me | Theorems.Thm_StochModelWC_ProxSubgrad_theorem_3_4_eq_3_14
-- name    : StochModelWC.ProxSubgrad.theorem_3_4_eq_3_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:47:11.783927+00:00
-- url     : https://prove2.me/theorems/f72ca2b8-c43a-4433-a890-55323b21dfc2
-- title:
--   Theorem 3.4, (3.14) — expected descent of the Moreau envelope along Algorithm 3.1
-- statement:
--   Assume the setting of §3: $r$ closed convex with nonempty domain $D$, $f$ $\rho$-weakly convex, $\varphi = f + r$, Assumption A with constant $L$, and $x_0 \in D$. Fix $\bar\rho \in (\rho, 2\rho]$ and stepsizes $\alpha_t \in (0, 1/\bar\rho]$ for $t = 0, \dots, T$, and let $x_t$ be the iterates of Algorithm 3.1 driven by i.i.d. samples $\xi_0, \dots, \xi_T \sim P$. Then for every $t \le T$ the quantities $\varphi_{1/\bar\rho}(x_{t+1})$, $\varphi_{1/\bar\rho}(x_t)$ and $\|\nabla\varphi_{1/\bar\rho}(x_t)\|^2$ are integrable and
--   $$\mathbb E\big[\varphi_{1/\bar\rho}(x_{t+1})\big] \le \mathbb E\big[\varphi_{1/\bar\rho}(x_t)\big] - \frac{\alpha_t(\bar\rho - \rho)}{\bar\rho}\,\mathbb E\big[\|\nabla\varphi_{1/\bar\rho}(x_t)\|^2\big] + 2\alpha_t^2\bar\rho L^2.$$
--
--   The paper prints the last term as $\alpha_t^2\bar\rho L^2$; its proof (and the unfolded sum leading to (3.15)) gives $2\alpha_t^2\bar\rho L^2$, which is the constant stated here. The estimate says the proximal stochastic subgradient method is an approximate descent method on the Moreau envelope.
--
--   **Formalization Note.** $\mathbb E$ is the integral against the product measure $P^{\otimes(T+1)}$ on sample paths. The proximal map is a function `prox` constrained to return a proximal point of $a r$ for every $a > 0$. Integrability of each integrand is part of the conclusion, so the inequality cannot hold by the convention that a non-integrable function has integral $0$.
-- source:
--   Davis–Drusvyatskiy, Stochastic Model-Based Minimization of Weakly Convex Functions, arXiv:1803.06523v3, p. 16, Theorem 3.4, (3.14) (constant as derived in its proof, p. 16)

import Mathlib
import Definitions.Def_StochModelWC_ProxSubgrad_Basic
import Definitions.Def_StochModelWC_ProxSubgrad_AssumptionA
import Definitions.Def_StochModelWC_ProxSubgrad_Algorithm31

open MeasureTheory Filter Topology

namespace StochModelWC.ProxSubgrad

/-- Theorem 3.4, (3.14) (p. 16), with the constant `2 α_t² ρ̄ L²` that its proof establishes (the paper
prints `α_t² ρ̄ L²`): along the run of Algorithm 3.1 on `T + 1` i.i.d. samples, for every `t ≤ T`,
`E[φ_{1/ρ̄}(x_{t+1})] ≤ E[φ_{1/ρ̄}(x_t)] − α_t(ρ̄ − ρ)/ρ̄ · E‖∇φ_{1/ρ̄}(x_t)‖² + 2 α_t² ρ̄ L²`. -/
theorem theorem_3_4_eq_3_14 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (U D : Set (EuclideanSpace ℝ (Fin d))) (f r : EuclideanSpace ℝ (Fin d) → ℝ)
    (G : EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d)) (ρ L : ℝ)
    (hD : D.Nonempty) (hr_cl : StochModelWC.ModelBased.IsClosedFn D r) (hr_cvx : ConvexOn ℝ D r)
    (hf : StochModelWC.ModelBased.IsWeaklyConvexOn Set.univ ρ f) (hA : AssumptionA P U D f G L)
    (prox : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hprox : ∀ a : ℝ, 0 < a → ∀ z, StochModelWC.ModelBased.IsProxPt D r a z (prox a z))
    (x0 : EuclideanSpace ℝ (Fin d)) (hx0 : x0 ∈ D) (T : ℕ) (α : ℕ → ℝ)
    (ρbar : ℝ) (hρbar : ρ < ρbar) (hρbar2 : ρbar ≤ 2 * ρ)
    (hα : ∀ t ≤ T, 0 < α t ∧ α t ≤ 1 / ρbar) :
    ∀ t ≤ T,
      Integrable (fun ω => StochModelWC.ModelBased.moreauEnv D (fun y => f y + r y) (1 / ρbar)
        (proxSGIter prox G α x0 ω (t + 1))) (Measure.pi (fun _ : Fin (T + 1) => P)) ∧
      Integrable (fun ω => StochModelWC.ModelBased.moreauEnv D (fun y => f y + r y) (1 / ρbar)
        (proxSGIter prox G α x0 ω t)) (Measure.pi (fun _ : Fin (T + 1) => P)) ∧
      Integrable (fun ω => ‖gradient (StochModelWC.ModelBased.moreauEnv D (fun y => f y + r y) (1 / ρbar))
        (proxSGIter prox G α x0 ω t)‖ ^ 2) (Measure.pi (fun _ : Fin (T + 1) => P)) ∧
      ∫ ω, StochModelWC.ModelBased.moreauEnv D (fun y => f y + r y) (1 / ρbar) (proxSGIter prox G α x0 ω (t + 1))
          ∂(Measure.pi (fun _ : Fin (T + 1) => P)) ≤
        ∫ ω, StochModelWC.ModelBased.moreauEnv D (fun y => f y + r y) (1 / ρbar) (proxSGIter prox G α x0 ω t)
          ∂(Measure.pi (fun _ : Fin (T + 1) => P))
        - α t * (ρbar - ρ) / ρbar *
          ∫ ω, ‖gradient (StochModelWC.ModelBased.moreauEnv D (fun y => f y + r y) (1 / ρbar))
            (proxSGIter prox G α x0 ω t)‖ ^ 2 ∂(Measure.pi (fun _ : Fin (T + 1) => P))
        + 2 * α t ^ 2 * ρbar * L ^ 2 := by sorry

end StochModelWC.ProxSubgrad
