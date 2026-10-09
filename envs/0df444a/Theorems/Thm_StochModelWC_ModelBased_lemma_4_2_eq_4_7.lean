-- Prove2me | Theorems.Thm_StochModelWC_ModelBased_lemma_4_2_eq_4_7
-- name    : StochModelWC.ModelBased.lemma_4_2_eq_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:51:08.643437+00:00
-- url     : https://prove2.me/theorems/52603c99-8aec-4908-aeb8-1a9e888cc3c8
-- title:
--   Lemma 4.2, (4.7) — one-step contraction of Algorithm 4.1 towards the proximal point
-- statement:
--   Work under Assumption B for $\varphi=f+r$ ($r$ closed and proper with domain $D$, $f$ locally Lipschitz). Fix $\bar\rho>\tau+\eta$ with $\bar\rho>0$, and a parameter $\beta>\bar\rho$ with $\beta>\eta$. Let $x\in U$ be the current iterate, let $\hat x=\operatorname{prox}_{\varphi/\bar\rho}(x)$ be a proximal point of $\varphi$ at $x$ (a minimizer over $D$ of $y\mapsto\varphi(y)+\frac{\bar\rho}{2}\|y-x\|^2$), and let $x^+=s(\xi)$ be the next iterate of Algorithm 4.1 generated from a fresh sample $\xi\sim P$: $s$ is measurable, takes values in $D$, and for almost every $\xi$ minimizes $y\mapsto r(y)+f_x(y,\xi)+\frac{\beta}{2}\|y-x\|^2$ over $D$. Then $\|\hat x-x^+\|^2$ is integrable and
--   $$\mathbb E_\xi\|\hat x-x^+\|^2\le\|\hat x-x\|^2-\frac{\bar\rho-\tau-\eta}{\beta-\eta}\|\hat x-x\|^2+\frac{4\mathsf L^2}{(\beta-\eta)(\beta-\bar\rho)}. \tag{4.7}$$
--
--   In the paper this is estimate (4.7) of Lemma 4.2 at step $t$, with $x=x_t$, $\beta=\beta_t$, $x^+=x_{t+1}$, where $\mathbb E_t$ is the expectation conditioned on $\xi_0,\dots,\xi_{t-1}$. It says that one step of the method moves the iterate closer to its proximal point in expectation, up to a noise term; it is the key input to the descent estimate (4.14) on the Moreau envelope.
--
--   **Formalization Note** Because $\xi_t$ is independent of the past, the conditional expectation $\mathbb E_t$ is written as the integral over one sample $\xi\sim P$ with the current point $x$ held fixed (an arbitrary point of $U$). The hypotheses $\beta>\eta$ and $\bar\rho>0$ are implicit in the paper: its proof uses that the subproblem is $(\beta-\eta)$-strongly convex and divides by $\beta-\eta$ (Assumption B allows any real $\tau$, so $\beta>\bar\rho>\tau+\eta$ does not give $\beta>\eta$ when $\tau<0$, and (4.7) can then fail), and $\bar\rho>0$ makes $\operatorname{prox}_{\varphi/\bar\rho}$ meaningful.
-- source:
--   Davis–Drusvyatskiy, Stochastic Model-Based Minimization of Weakly Convex Functions, arXiv:1803.06523v3, p. 20, Lemma 4.2, (4.7)

import Mathlib
import Definitions.Def_StochModelWC_ModelBased_Basic
import Definitions.Def_StochModelWC_ModelBased_AssumptionB

open MeasureTheory Filter Topology

namespace StochModelWC.ModelBased

/-- Lemma 4.2, estimate (4.7) (p. 20), one step conditional on the past: the current iterate `x ∈ U` is held fixed,
`x̂ = prox_{φ/ρ̄}(x)`, and `s ξ` is the next iterate of Algorithm 4.1 with stepsize parameter `β` driven by the
fresh sample `ξ ∼ P` (so `E_t` is `∫ · ∂P`). -/
theorem lemma_4_2_eq_4_7 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U D : Set (EuclideanSpace ℝ (Fin d))) (f r : EuclideanSpace ℝ (Fin d) → ℝ)
    (model : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (τ η L : ℝ) (Lfun : Ω → ℝ)
    (hD : D.Nonempty) (hr : IsClosedFn D r) (hf : LocallyLipschitz f)
    (hB : AssumptionB P U D f r model τ η L Lfun)
    (ρbar : ℝ) (hρbar : τ + η < ρbar) (hρbar0 : 0 < ρbar)
    (β : ℝ) (hβ : ρbar < β) (hβη : η < β)
    (x xhat : EuclideanSpace ℝ (Fin d)) (hx : x ∈ U)
    (hxhat : IsProxPt D (fun y => f y + r y) (1 / ρbar) x xhat)
    (s : Ω → EuclideanSpace ℝ (Fin d)) (hs_meas : Measurable s) (hsD : ∀ ξ, s ξ ∈ D)
    (hs_min : ∀ᵐ ξ ∂P, IsMinOn (fun y => r y + model x y ξ + β / 2 * ‖y - x‖ ^ 2) D (s ξ)) :
    Integrable (fun ξ => ‖xhat - s ξ‖ ^ 2) P ∧
      ∫ ξ, ‖xhat - s ξ‖ ^ 2 ∂P ≤
        ‖xhat - x‖ ^ 2 - (ρbar - τ - η) / (β - η) * ‖xhat - x‖ ^ 2
          + 4 * L ^ 2 / ((β - η) * (β - ρbar)) := by sorry

end StochModelWC.ModelBased
