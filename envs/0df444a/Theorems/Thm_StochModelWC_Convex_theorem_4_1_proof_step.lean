-- Prove2me | Theorems.Thm_StochModelWC_Convex_theorem_4_1_proof_step
-- name    : StochModelWC.Convex.theorem_4_1_proof_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:45:57.204014+00:00
-- url     : https://prove2.me/theorems/b26dcbe7-b387-4c12-b2ea-69619c38cbcc
-- title:
--   Proof of Theorem 4.1, first display — 2α_t E[φ(x_{t+1}) − φ(x*)] ≤ E‖x_t − x*‖² − E‖x_{t+1} − x*‖² + 4𝖫²α_t²
-- statement:
--   Work in the convex setting of Theorem 4.1: Assumption B holds with $\tau=\eta=0$ (the models lower-bound $f$ in expectation and $f_x(\cdot,\xi)+r$ is convex), $D=\operatorname{dom}r$ is nonempty, $r$ is closed and $f$ is locally Lipschitz. Run Algorithm 4.1 from $x_0\in U$ with parameters $\beta_t=\alpha_t^{-1}$, $\alpha_t>0$, on i.i.d. samples $\xi_0,\dots,\xi_T\sim P$, and let $x^*\in D$ be any minimizer of $\varphi=f+r$. Then for every $t\in\{0,\dots,T\}$ the quantities $\varphi(x_{t+1})$, $\|x_t-x^*\|^2$ and $\|x_{t+1}-x^*\|^2$ are integrable and
--   $$2\alpha_t\,\mathbb E\big[\varphi(x_{t+1})-\varphi(x^*)\big]\le\mathbb E\|x_t-x^*\|^2-\mathbb E\big[\|x_{t+1}-x^*\|^2\big]+4\mathsf L^2\alpha_t^2 .$$
--
--   Summing over $t=0,\dots,T$ telescopes the distance terms; this is the step from the one-step estimate (4.8) to the rate of Theorem 4.1.
--
--   **Formalization Note** The paper prints $2\mathsf L^2\alpha_t^2$; it is obtained by setting $\eta=0$, $x=x^*$ in (4.8), and the constant the proof of (4.8) establishes gives $4\mathsf L^2\alpha_t^2$. The printed version fails already for one step (same example as in (4.8): $x_0=x^*=0$, $\alpha_0=1$ gives $2\le1$). Expectations are integrals against the product measure $P^{\otimes(T+1)}$; the iterates are the run of a jointly measurable selection of the argmin step. Integrability of every integrand is part of the conclusion.
-- source:
--   Davis–Drusvyatskiy, Stochastic Model-Based Minimization of Weakly Convex Functions, arXiv:1803.06523v3, p. 23, proof of Theorem 4.1, first display

import Mathlib
import Definitions.Def_StochModelWC_ModelBased_Basic
import Definitions.Def_StochModelWC_ModelBased_AssumptionB

open MeasureTheory Filter Topology

namespace StochModelWC.Convex

/-- Proof of Theorem 4.1, first display (p. 23): in the convex setting (`τ = η = 0`), along Algorithm 4.1 with
`β_t = α_t⁻¹` (StochModelWC.ModelBased.run on `T + 1` i.i.d. samples `ω = (ξ₀, …, ξ_T) ∼ P^{⊗(T+1)}`) and for any minimizer `x*` of
`φ = f + r`, every step `t ≤ T` satisfies
`2 α_t E[φ(x_{t+1}) − φ(x*)] ≤ E‖x_t − x*‖² − E‖x_{t+1} − x*‖² + 4 L² α_t²`,
with all three expectations of integrable functions. The paper prints `2 L² α_t²`; its proof (estimate (4.8) as
derived on p. 21) yields `4 L² α_t²`, and the printed constant fails in general. -/
theorem theorem_4_1_proof_step {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
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
    (hmin : ∀ y ∈ D, f xstar + r xstar ≤ f y + r y) (T : ℕ) :
    ∀ t ≤ T,
      Integrable (fun ω : Fin (T + 1) → Ω =>
          f (StochModelWC.ModelBased.run upd x0 ω (t + 1)) + r (StochModelWC.ModelBased.run upd x0 ω (t + 1)))
        (Measure.pi fun _ : Fin (T + 1) => P) ∧
      Integrable (fun ω : Fin (T + 1) → Ω => ‖StochModelWC.ModelBased.run upd x0 ω t - xstar‖ ^ 2)
        (Measure.pi fun _ : Fin (T + 1) => P) ∧
      Integrable (fun ω : Fin (T + 1) → Ω => ‖StochModelWC.ModelBased.run upd x0 ω (t + 1) - xstar‖ ^ 2)
        (Measure.pi fun _ : Fin (T + 1) => P) ∧
      2 * α t * ∫ ω, (f (StochModelWC.ModelBased.run upd x0 ω (t + 1)) + r (StochModelWC.ModelBased.run upd x0 ω (t + 1)) - (f xstar + r xstar))
          ∂(Measure.pi fun _ : Fin (T + 1) => P) ≤
        ∫ ω, ‖StochModelWC.ModelBased.run upd x0 ω t - xstar‖ ^ 2 ∂(Measure.pi fun _ : Fin (T + 1) => P)
          - ∫ ω, ‖StochModelWC.ModelBased.run upd x0 ω (t + 1) - xstar‖ ^ 2 ∂(Measure.pi fun _ : Fin (T + 1) => P)
          + 4 * L ^ 2 * α t ^ 2 := by sorry

end StochModelWC.Convex
