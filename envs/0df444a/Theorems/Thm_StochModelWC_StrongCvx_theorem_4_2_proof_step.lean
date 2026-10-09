-- Prove2me | Theorems.Thm_StochModelWC_StrongCvx_theorem_4_2_proof_step
-- name    : StochModelWC.StrongCvx.theorem_4_2_proof_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:41:59.070901+00:00
-- url     : https://prove2.me/theorems/220d2dd7-142d-41b3-871d-12d24ae2d230
-- title:
--   Proof of Theorem 4.2, first display — E[φ(x_{t+1}) − φ(x*)] ≤ β_tΔ_t − (β_t + µ)Δ_{t+1} + 2𝖫²/β_t
-- statement:
--   Work in the strongly convex setting of Theorem 4.2: Assumption B holds with $\tau=0$ and $\eta=-\mu$ for some $\mu>0$ (the models lower-bound $f$ in expectation and $f_x(\cdot,\xi)+r$ is $\mu$-strongly convex), $D=\operatorname{dom}r$ is nonempty, $r$ is closed and $f$ is locally Lipschitz. Run Algorithm 4.1 from $x_0\in U$ with $\beta_t=\mu(t+1)/2$ on i.i.d. samples $\xi_0,\dots,\xi_T\sim P$, let $x^*\in D$ be any minimizer of $\varphi=f+r$, and set
--   $$\Delta_t:=\tfrac12\,\mathbb E\big[\|x^*-x_t\|^2\big].$$
--   Then for every $t\in\{0,\dots,T\}$ the quantities $\varphi(x_{t+1})$, $\|x^*-x_t\|^2$ and $\|x^*-x_{t+1}\|^2$ are integrable and
--   $$\mathbb E\big[\varphi(x_{t+1})-\varphi(x^*)\big]\le\beta_t\Delta_t-(\beta_t+\mu)\Delta_{t+1}+\frac{2\mathsf L^2}{\beta_t}.$$
--
--   With $\beta_t=\mu(t+1)/2$, multiplying by $t+2$ makes the distance terms telescope; this is the step from the one-step estimate (4.8) to the $O(1/(\mu T))$ rate of Theorem 4.2.
--
--   **Formalization Note** The paper prints $\mathsf L^2/\beta_t$; it is obtained by setting $\eta=-\mu$, $x=x^*$ in (4.8) and multiplying by $(\beta_t+\mu)/2$, and the constant $4\mathsf L^2/(\beta_t(\beta_t-\eta))$ that the proof of (4.8) establishes gives $2\mathsf L^2/\beta_t$. The printed (4.8) fails in general (see the milestone Lemma 4.2, (4.8)); whether the printed display itself fails for Algorithm 4.1 with this stepsize was not checked. Expectations are integrals against the product measure $P^{\otimes(T+1)}$; the iterates are the run of a jointly measurable selection of the argmin step. Integrability of every integrand is part of the conclusion. $\mu$-strong convexity of $f_x(\cdot,\xi)+r$ is encoded as $(-\mu)$-weak convexity, i.e. convexity of $f_x(\cdot,\xi)+r-\frac\mu2\|\cdot\|^2$ on $D$. The constant $\mathsf L$ is `L` in Lean and $L(\xi)$ is `Lfun`.
-- source:
--   Davis–Drusvyatskiy, Stochastic Model-Based Minimization of Weakly Convex Functions, arXiv:1803.06523v3, p. 23, proof of Theorem 4.2, first display

import Mathlib
import Definitions.Def_StochModelWC_ModelBased_Basic
import Definitions.Def_StochModelWC_ModelBased_AssumptionB

open MeasureTheory Filter Topology

namespace StochModelWC.StrongCvx

/-- Proof of Theorem 4.2, first display (p. 23): in the strongly convex setting (`τ = 0`, `f_x(·, ξ) + r`
`μ`-strongly convex, i.e. `η = -μ`), along Algorithm 4.1 with `β_t = μ (t + 1) / 2` (run on `T + 1` i.i.d. samples
`ω = (ξ₀, …, ξ_T) ∼ P^{⊗(T+1)}`) and for any minimizer `x*` of `φ = f + r`, every step `t ≤ T` satisfies
`E[φ(x_{t+1}) − φ(x*)] ≤ β_t Δ_t − (β_t + μ) Δ_{t+1} + 2 L² / β_t` with `Δ_t = ½ E‖x* − x_t‖²`,
all expectations being of integrable functions. The paper prints `L² / β_t`; its proof (estimate (4.8) as derived
on p. 21, constant `4L²/(β_t(β_t − η))`) yields `2 L² / β_t`; the printed constant comes from the printed (4.8),
which fails in general. -/
theorem theorem_4_2_proof_step {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U D : Set (EuclideanSpace ℝ (Fin d))) (f r : EuclideanSpace ℝ (Fin d) → ℝ)
    (model : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (L : ℝ) (Lfun : Ω → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (hD : D.Nonempty) (hr : StochModelWC.ModelBased.IsClosedFn D r) (hf : LocallyLipschitz f)
    (hB : StochModelWC.ModelBased.AssumptionB P U D f r model 0 (-μ) L Lfun)
    (upd : ℕ → EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d))
    (hupd : StochModelWC.ModelBased.IsAlg41Step P U D r model (fun t => μ * ((t : ℝ) + 1) / 2) upd)
    (x0 : EuclideanSpace ℝ (Fin d)) (hx0 : x0 ∈ U)
    (xstar : EuclideanSpace ℝ (Fin d)) (hxstar : xstar ∈ D)
    (hmin : ∀ y ∈ D, f xstar + r xstar ≤ f y + r y) (T : ℕ) :
    ∀ t ≤ T,
      Integrable (fun ω : Fin (T + 1) → Ω =>
          f (StochModelWC.ModelBased.run upd x0 ω (t + 1)) + r (StochModelWC.ModelBased.run upd x0 ω (t + 1)))
        (Measure.pi fun _ : Fin (T + 1) => P) ∧
      Integrable (fun ω : Fin (T + 1) → Ω => ‖xstar - StochModelWC.ModelBased.run upd x0 ω t‖ ^ 2)
        (Measure.pi fun _ : Fin (T + 1) => P) ∧
      Integrable (fun ω : Fin (T + 1) → Ω => ‖xstar - StochModelWC.ModelBased.run upd x0 ω (t + 1)‖ ^ 2)
        (Measure.pi fun _ : Fin (T + 1) => P) ∧
      ∫ ω, (f (StochModelWC.ModelBased.run upd x0 ω (t + 1)) + r (StochModelWC.ModelBased.run upd x0 ω (t + 1)) - (f xstar + r xstar))
          ∂(Measure.pi fun _ : Fin (T + 1) => P) ≤
        μ * ((t : ℝ) + 1) / 2 *
            (1 / 2 * ∫ ω, ‖xstar - StochModelWC.ModelBased.run upd x0 ω t‖ ^ 2 ∂(Measure.pi fun _ : Fin (T + 1) => P))
          - (μ * ((t : ℝ) + 1) / 2 + μ) *
            (1 / 2 * ∫ ω, ‖xstar - StochModelWC.ModelBased.run upd x0 ω (t + 1)‖ ^ 2 ∂(Measure.pi fun _ : Fin (T + 1) => P))
          + 2 * L ^ 2 / (μ * ((t : ℝ) + 1) / 2) := by sorry

end StochModelWC.StrongCvx
