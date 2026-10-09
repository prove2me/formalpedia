-- Prove2me | Theorems.Thm_StochModelWC_StrongCvx_lemma_4_2_eq_4_8
-- name    : StochModelWC.StrongCvx.lemma_4_2_eq_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:41:51.582966+00:00
-- url     : https://prove2.me/theorems/e05919dc-3880-4897-b26b-304d0c574964
-- title:
--   Lemma 4.2, (4.8) — one-step distance estimate against an arbitrary point of dom r
-- statement:
--   Work under Assumption B with constants $\tau,\eta,\mathsf L$ for the problem $\min\varphi=f+r$, with $D=\operatorname{dom}r$ nonempty, $r$ closed and $f$ locally Lipschitz. Fix a current point $x_t\in U$, a parameter $\beta>0$ with $\beta>\eta$, and let
--   $$x_{t+1}(\xi)\in\operatorname*{argmin}_{y\in D}\Big\{r(y)+f_{x_t}(y,\xi)+\frac{\beta}{2}\|y-x_t\|^2\Big\}$$
--   be a measurable selection of the step of Algorithm 4.1 driven by a fresh sample $\xi\sim P$ (a minimizer for almost every $\xi$, a point of $D$ always), with $\xi\mapsto r(x_{t+1}(\xi))$ integrable. Write $\mathbb E_t$ for the expectation over $\xi$. Then for every $x\in D$ the function $\xi\mapsto\|x_{t+1}(\xi)-x\|^2$ and $\xi\mapsto\varphi(x_{t+1}(\xi))$ are integrable and
--   $$\mathbb E_t\big[\|x_{t+1}-x\|^2\big]\le\frac{\beta+\tau}{\beta-\eta}\|x_t-x\|^2-\frac{2}{\beta-\eta}\,\mathbb E_t\big[\varphi(x_{t+1})-\varphi(x)\big]+\frac{4\mathsf L^2}{\beta(\beta-\eta)}.$$
--
--   This is the descent estimate in function values: specialized to $\eta=0$ and $x$ a minimizer of $\varphi$, it gives the one-step inequality behind the $O(1/\sqrt T)$ rate of Theorem 4.1 (and, with $\eta=-\mu$, the $O(1/(\mu T))$ rate of Theorem 4.2).
--
--   **Formalization Note** The paper prints the last term of (4.8) as $\frac{2\mathsf L^2}{\beta_t(\beta_t-\eta)}$; its proof (p. 21) bounds the $\delta$-dependent terms by $\frac{2\mathsf L^2}{\beta_t}$ and then divides by $\frac{\beta_t-\eta}{2}$, which yields $\frac{4\mathsf L^2}{\beta_t(\beta_t-\eta)}$. The printed constant fails: with $d=1$, $r=0$, $f(y)=|y|$, the model $f_0(y,\xi)=g(\xi)y$ with $g=\pm1$ equally likely (and $f_x(y,\xi)=\operatorname{sign}(x)\,y$ for $x\ne0$), $L(\xi)\equiv\mathsf L=1$, $\tau=\eta=0$, $\beta=1$, $x_t=x=0$, the left side is $1$ while the printed right side is $0$. The same failure occurs with $\eta<0$: adding $r(y)=\frac{\mu}{2}y^2$ to that example ($\tau=0$, $\eta=-\mu$, $\mu=1$, $\beta=10$) gives left side $1/121$ and printed right side $2/110-2/121-1/1331<1/121$. The statement is the one the proof establishes. Conditioning on the past is expressed by holding $x_t$ fixed and integrating over one sample, since $\xi_t$ is independent of $\xi_0,\dots,\xi_{t-1}$. The hypotheses $\beta>0$ and $\beta>\eta$ hold in Algorithm 4.1 whenever $\tau\ge0$; they are stated directly because $\eta$ may be negative. Integrability of $r$ along the step is a hypothesis: the expectation $\mathbb E_t[\varphi(x_{t+1})]$ of the page presupposes it.
-- source:
--   Davis–Drusvyatskiy, Stochastic Model-Based Minimization of Weakly Convex Functions, arXiv:1803.06523v3, p. 20, Lemma 4.2, (4.8); proof on pp. 20–21

import Mathlib
import Definitions.Def_StochModelWC_ModelBased_Basic
import Definitions.Def_StochModelWC_ModelBased_AssumptionB

open MeasureTheory Filter Topology

namespace StochModelWC.StrongCvx

/-- Lemma 4.2, estimate (4.8) (p. 20), one step conditional on the past: the current iterate `xc ∈ U` is held
fixed, `s ξ` is the next iterate of Algorithm 4.1 with parameter `β` driven by the fresh sample `ξ ∼ P` (so `E_t`
is `∫ · ∂P`), and `x ∈ dom r = D` is an arbitrary comparison point. The constant is `4L²/(β(β − η))`, the one the
paper's proof (p. 21) yields; the display prints `2L²/(β(β − η))`, which fails in general. Integrability of
`r ∘ s` is an added hypothesis (the expectation `E_t[φ(x_{t+1})]` of the page presupposes it). -/
theorem lemma_4_2_eq_4_8 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U D : Set (EuclideanSpace ℝ (Fin d))) (f r : EuclideanSpace ℝ (Fin d) → ℝ)
    (model : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (τ η L : ℝ) (Lfun : Ω → ℝ)
    (hD : D.Nonempty) (hr : StochModelWC.ModelBased.IsClosedFn D r) (hf : LocallyLipschitz f)
    (hB : StochModelWC.ModelBased.AssumptionB P U D f r model τ η L Lfun)
    (β : ℝ) (hβ0 : 0 < β) (hβη : η < β)
    (xc : EuclideanSpace ℝ (Fin d)) (hxc : xc ∈ U)
    (s : Ω → EuclideanSpace ℝ (Fin d)) (hs_meas : Measurable s) (hsD : ∀ ξ, s ξ ∈ D)
    (hs_min : ∀ᵐ ξ ∂P, IsMinOn (fun y => r y + model xc y ξ + β / 2 * ‖y - xc‖ ^ 2) D (s ξ))
    (hrs : Integrable (fun ξ => r (s ξ)) P)
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ D) :
    Integrable (fun ξ => ‖s ξ - x‖ ^ 2) P ∧
      Integrable (fun ξ => f (s ξ) + r (s ξ)) P ∧
      ∫ ξ, ‖s ξ - x‖ ^ 2 ∂P ≤
        (β + τ) / (β - η) * ‖xc - x‖ ^ 2
          - 2 / (β - η) * ∫ ξ, (f (s ξ) + r (s ξ) - (f x + r x)) ∂P
          + 4 * L ^ 2 / (β * (β - η)) := by sorry

end StochModelWC.StrongCvx
