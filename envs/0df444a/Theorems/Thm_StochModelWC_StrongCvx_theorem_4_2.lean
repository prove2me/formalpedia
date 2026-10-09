-- Prove2me | Theorems.Thm_StochModelWC_StrongCvx_theorem_4_2
-- name    : StochModelWC.StrongCvx.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:42:17.941673+00:00
-- url     : https://prove2.me/theorems/e00f2ccb-b851-4ffb-a2b9-5199a38ce233
-- title:
--   Theorem 4.2 — under µ-strong convexity, E[φ(x̄_T) − φ(x*)] ≤ µ‖x₀−x*‖²/(T+2)² + 16𝖫²/(µ(T+2))
-- statement:
--   **Setting.** Minimize $\varphi=f+r$ over $\mathbb R^d$, where $r:\mathbb R^d\to\mathbb R\cup\{\infty\}$ is closed with nonempty domain $D$ and $f$ is locally Lipschitz. Suppose Assumption B holds with $\tau=0$ and with the functions $f_x(\cdot,\xi)+r(\cdot)$ $\mu$-strongly convex for some $\mu>0$ ($\eta=-\mu$): stochastic models $f_x(\cdot,\xi)$, exact in expectation at the base point and lower-bounding $f$ in expectation, with a random Lipschitz constant $L(\xi)$ satisfying $\sqrt{\mathbb E L(\xi)^2}\le\mathsf L$. Run Algorithm 4.1 from $x_0\in U$ with $\beta_t=\mu(t+1)/2$,
--   $$x_{t+1}=\operatorname*{argmin}_{x}\Big\{r(x)+f_{x_t}(x,\xi_t)+\frac{\mu(t+1)}{4}\|x-x_t\|^2\Big\},\qquad t=0,\dots,T,$$
--   on i.i.d. samples $\xi_t\sim P$. Let $x^*$ be any minimizer of $\varphi$.
--
--   **Conclusion.** For every integer $T>0$, the function inside the expectation below is integrable and
--   $$\mathbb E\Big[\varphi\Big(\frac{2}{(T+2)(T+3)-2}\sum_{t=1}^{T+1}(t+1)\,x_t\Big)-\varphi(x^*)\Big]\le\frac{\mu\|x_0-x^*\|^2}{(T+2)^2}+\frac{16\mathsf L^2}{\mu(T+2)}.$$
--   The weights $\frac{2(t+1)}{(T+2)(T+3)-2}$, $t=1,\dots,T+1$, sum to one, so the averaged point lies in $D$.
--
--   The theorem gives the $O(1/(\mu T))$ function-gap rate for stochastic model-based minimization (stochastic proximal point, prox-linear and proximal subgradient methods) under strong convexity, extending the nonuniform averaging technique of Schmidt, Le Roux and Bach to the fully proximal setting.
--
--   **Formalization Note** The paper prints $8\mathsf L^2$ in place of $16\mathsf L^2$. Its proof sums the first display of the proof (p. 23), which comes from (4.8); the proof of (4.8) yields the constant $4\mathsf L^2/(\beta_t(\beta_t-\eta))$, not the printed $2\mathsf L^2/(\beta_t(\beta_t-\eta))$, and this doubles the $\mathsf L^2$ term of the final bound. The statement is what the proof establishes; whether the printed bound with $8\mathsf L^2$ also holds was not settled. Expectations are integrals against $P^{\otimes(T+1)}$; the minimizer $x^*$ is a point of $D$ with $\varphi(x^*)\le\varphi(y)$ for all $y\in D$. The paper's $\bar\rho$ of Algorithm 4.1 does not affect the iterates: any $\bar\rho\in(-\mu,\mu/2)$ satisfies $\beta_t>\bar\rho>\tau+\eta=-\mu$ for every $t$. $\mu$-strong convexity is encoded as $(-\mu)$-weak convexity, which in a Euclidean space is the same notion. The constant $\mathsf L$ is `L` in Lean and $L(\xi)$ is `Lfun`.
-- source:
--   Davis–Drusvyatskiy, Stochastic Model-Based Minimization of Weakly Convex Functions, arXiv:1803.06523v3, p. 23, Theorem 4.2 and its proof, (4.19); p. 19, Algorithm 4.1

import Mathlib
import Definitions.Def_StochModelWC_ModelBased_Basic
import Definitions.Def_StochModelWC_ModelBased_AssumptionB

open MeasureTheory Filter Topology

namespace StochModelWC.StrongCvx

/-- Theorem 4.2 (p. 23): in the strongly convex setting (`τ = 0`, `f_x(·, ξ) + r` `μ`-strongly convex for some
`μ > 0`, i.e. Assumption B with `η = -μ`), Algorithm 4.1 with `β_t = μ (t + 1) / 2`, run on `T + 1` i.i.d. samples
`ω = (ξ₀, …, ξ_T) ∼ P^{⊗(T+1)}`, satisfies, for every `T > 0` and any minimizer `x*` of `φ = f + r`,
`E[φ(x̄_T) − φ(x*)] ≤ μ‖x₀ − x*‖² / (T + 2)² + 16 L² / (μ (T + 2))`,
where `x̄_T = 2 / ((T + 2)(T + 3) − 2) · Σ_{t=1}^{T+1} (t + 1) x_t` (weights summing to one, so `x̄_T ∈ D`), and
`φ(x̄_T)` is integrable. The paper prints `8 L²`; its proof, run with the constant of (4.8) that the proof of
Lemma 4.2 (p. 21) establishes, yields `16 L²`. -/
theorem theorem_4_2 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U D : Set (EuclideanSpace ℝ (Fin d))) (f r : EuclideanSpace ℝ (Fin d) → ℝ)
    (model : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (L : ℝ) (Lfun : Ω → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (hD : D.Nonempty) (hr : StochModelWC.ModelBased.IsClosedFn D r) (hf : LocallyLipschitz f)
    (hB : StochModelWC.ModelBased.AssumptionB P U D f r model 0 (-μ) L Lfun)
    (upd : ℕ → EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d))
    (hupd : StochModelWC.ModelBased.IsAlg41Step P U D r model (fun t => μ * ((t : ℝ) + 1) / 2) upd)
    (x0 : EuclideanSpace ℝ (Fin d)) (hx0 : x0 ∈ U)
    (xstar : EuclideanSpace ℝ (Fin d)) (hxstar : xstar ∈ D)
    (hmin : ∀ y ∈ D, f xstar + r xstar ≤ f y + r y)
    (T : ℕ) (hT : 0 < T) :
    Integrable (fun ω : Fin (T + 1) → Ω =>
        f ((2 / (((T : ℝ) + 2) * ((T : ℝ) + 3) - 2)) •
            ∑ t ∈ Finset.Icc 1 (T + 1), ((t : ℝ) + 1) • StochModelWC.ModelBased.run upd x0 ω t)
          + r ((2 / (((T : ℝ) + 2) * ((T : ℝ) + 3) - 2)) •
            ∑ t ∈ Finset.Icc 1 (T + 1), ((t : ℝ) + 1) • StochModelWC.ModelBased.run upd x0 ω t))
      (Measure.pi fun _ : Fin (T + 1) => P) ∧
    ∫ ω, (f ((2 / (((T : ℝ) + 2) * ((T : ℝ) + 3) - 2)) •
              ∑ t ∈ Finset.Icc 1 (T + 1), ((t : ℝ) + 1) • StochModelWC.ModelBased.run upd x0 ω t)
            + r ((2 / (((T : ℝ) + 2) * ((T : ℝ) + 3) - 2)) •
              ∑ t ∈ Finset.Icc 1 (T + 1), ((t : ℝ) + 1) • StochModelWC.ModelBased.run upd x0 ω t)
            - (f xstar + r xstar)) ∂(Measure.pi fun _ : Fin (T + 1) => P) ≤
      μ * ‖x0 - xstar‖ ^ 2 / ((T : ℝ) + 2) ^ 2 + 16 * L ^ 2 / (μ * ((T : ℝ) + 2)) := by sorry

end StochModelWC.StrongCvx
