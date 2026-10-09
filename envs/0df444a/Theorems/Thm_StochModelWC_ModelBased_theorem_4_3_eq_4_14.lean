-- Prove2me | Theorems.Thm_StochModelWC_ModelBased_theorem_4_3_eq_4_14
-- name    : StochModelWC.ModelBased.theorem_4_3_eq_4_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:51:10.646383+00:00
-- url     : https://prove2.me/theorems/cd445cc8-f7f2-40e4-b5e4-9a70e9bda38a
-- title:
--   Theorem 4.3, (4.14) — expected descent of the Moreau envelope along Algorithm 4.1
-- statement:
--   Work under Assumption B for $\varphi=f+r$ ($r$ closed and proper with domain $D\subseteq U$, $f$ locally Lipschitz). Fix a real $\bar\rho>\tau+\eta$ with $\bar\rho>0$ and a sequence $(\beta_t)_{t\ge0}$ with $\beta_t>\bar\rho$ and $\beta_t>\eta$ for all $t$. Run Algorithm 4.1 from $x_0\in U$ on i.i.d. samples $\xi_0,\dots,\xi_T\sim P$:
--   $$x_{t+1}=\operatorname*{argmin}_x\Big\{r(x)+f_{x_t}(x,\xi_t)+\frac{\beta_t}{2}\|x-x_t\|^2\Big\}.$$
--   Then for every $t\in\{0,\dots,T\}$ the quantities below are integrable and
--   $$\mathbb E\big[\varphi_{1/\bar\rho}(x_{t+1})\big]\le\mathbb E\big[\varphi_{1/\bar\rho}(x_t)\big]-\frac{\bar\rho-\tau-\eta}{2\bar\rho(\beta_t-\eta)}\,\mathbb E\big[\|\nabla\varphi_{1/\bar\rho}(x_t)\|^2\big]+\frac{2\bar\rho\mathsf L^2}{(\beta_t-\eta)(\beta_t-\bar\rho)}. \tag{4.14}$$
--
--   The Moreau envelope $\varphi_{1/\bar\rho}$ thus acts as a Lyapunov function for the method: in expectation it decreases by a multiple of the squared stationarity measure, up to a noise term. Summing (4.14) over $t$ gives the rate (4.15).
--
--   **Formalization Note** The samples form a point $\omega=(\xi_0,\dots,\xi_T)$ of $\Omega^{T+1}$ under the product measure, and $\mathbb E$ is the integral against it. The update is any measurable selection of the argmin (as in the definition of the step of Algorithm 4.1). $\nabla\varphi_{1/\bar\rho}$ is Mathlib's `gradient`, which agrees with the true gradient by Lemma 2.2. Integrability of each integrand is part of the conclusion. $\beta_t>\eta$ (the subproblem is $(\beta_t-\eta)$-strongly convex; automatic when $\tau\ge0$, but Assumption B allows any real $\tau$), $\bar\rho>0$ and $x_0\in U$ are implicit in the paper.
-- source:
--   Davis–Drusvyatskiy, Stochastic Model-Based Minimization of Weakly Convex Functions, arXiv:1803.06523v3, p. 21, Theorem 4.3, (4.14)

import Mathlib
import Definitions.Def_StochModelWC_ModelBased_Basic
import Definitions.Def_StochModelWC_ModelBased_AssumptionB

open MeasureTheory Filter Topology

namespace StochModelWC.ModelBased

/-- Theorem 4.3, estimate (4.14) (p. 21): along Algorithm 4.1 (run on `T + 1` i.i.d. samples
`ω = (ξ₀, …, ξ_T) ∼ P^{⊗(T+1)}`), the Moreau envelope `φ_{1/ρ̄}` decreases in expectation by a multiple of the
expected squared gradient, up to `2ρ̄L²/((β_t − η)(β_t − ρ̄))`, at every step `t ≤ T`. -/
theorem theorem_4_3_eq_4_14 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U D : Set (EuclideanSpace ℝ (Fin d))) (f r : EuclideanSpace ℝ (Fin d) → ℝ)
    (model : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (τ η L : ℝ) (Lfun : Ω → ℝ)
    (hD : D.Nonempty) (hr : IsClosedFn D r) (hf : LocallyLipschitz f)
    (hB : AssumptionB P U D f r model τ η L Lfun)
    (ρbar : ℝ) (hρbar : τ + η < ρbar) (hρbar0 : 0 < ρbar)
    (β : ℕ → ℝ) (hβ : ∀ t, ρbar < β t) (hβη : ∀ t, η < β t)
    (upd : ℕ → EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d))
    (hupd : IsAlg41Step P U D r model β upd)
    (x0 : EuclideanSpace ℝ (Fin d)) (hx0 : x0 ∈ U) (T : ℕ) :
    ∀ t ≤ T,
      Integrable (fun ω : Fin (T + 1) → Ω =>
          moreauEnv D (fun y => f y + r y) (1 / ρbar) (run upd x0 ω (t + 1)))
        (Measure.pi fun _ : Fin (T + 1) => P) ∧
      Integrable (fun ω : Fin (T + 1) → Ω =>
          moreauEnv D (fun y => f y + r y) (1 / ρbar) (run upd x0 ω t))
        (Measure.pi fun _ : Fin (T + 1) => P) ∧
      Integrable (fun ω : Fin (T + 1) → Ω =>
          ‖gradient (moreauEnv D (fun y => f y + r y) (1 / ρbar)) (run upd x0 ω t)‖ ^ 2)
        (Measure.pi fun _ : Fin (T + 1) => P) ∧
      ∫ ω, moreauEnv D (fun y => f y + r y) (1 / ρbar) (run upd x0 ω (t + 1))
          ∂(Measure.pi fun _ : Fin (T + 1) => P) ≤
        ∫ ω, moreauEnv D (fun y => f y + r y) (1 / ρbar) (run upd x0 ω t)
            ∂(Measure.pi fun _ : Fin (T + 1) => P)
          - (ρbar - τ - η) / (2 * ρbar * (β t - η)) *
            ∫ ω, ‖gradient (moreauEnv D (fun y => f y + r y) (1 / ρbar)) (run upd x0 ω t)‖ ^ 2
              ∂(Measure.pi fun _ : Fin (T + 1) => P)
          + 2 * ρbar * L ^ 2 / ((β t - η) * (β t - ρbar)) := by sorry

end StochModelWC.ModelBased
