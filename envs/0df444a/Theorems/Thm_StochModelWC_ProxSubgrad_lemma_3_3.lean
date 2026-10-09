-- Prove2me | Theorems.Thm_StochModelWC_ProxSubgrad_lemma_3_3
-- name    : StochModelWC.ProxSubgrad.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:46:47.754639+00:00
-- url     : https://prove2.me/theorems/51f99123-8700-4520-9ac0-c41a0694b7e7
-- title:
--   Lemma 3.3 — one-step contraction towards the proximal point
-- statement:
--   Assume the setting of §3: $r$ closed convex with nonempty domain $D$, $f$ $\rho$-weakly convex, $\varphi = f + r$, and Assumption A with constant $L$. Let $\bar\rho \in (\rho, 2\rho]$ and $\alpha \in (0, 1/\bar\rho]$. Fix $x \in D$ and let $\hat x = \operatorname{prox}_{\varphi/\bar\rho}(x)$. If $x^+ = \operatorname{prox}_{\alpha r}(x - \alpha G(x,\xi))$ is one step of Algorithm 3.1 with $\xi \sim P$, then $\|x^+ - \hat x\|^2$ is integrable and
--   $$\mathbb E_\xi\|x^+ - \hat x\|^2 \le \|x - \hat x\|^2 + 4\alpha^2L^2 - 2\alpha(\bar\rho - \rho)\|x - \hat x\|^2.$$
--
--   Applied at $x = x_t$ with $\alpha = \alpha_t$, this is the paper's estimate for $\mathbb E_t\|x_{t+1} - \hat x_t\|^2$, the conditional expectation given $\xi_0, \dots, \xi_{t-1}$. It is the descent property behind Theorem 3.4.
--
--   **Formalization Note.** The conditional expectation $\mathbb E_t$ is the integral over one sample $\xi \sim P$ with the current iterate held fixed at an arbitrary point $x \in D$. The proximal map is a function `prox` with `prox a z` a proximal point of $a r$ at $z$ for every $a > 0$.
-- source:
--   Davis–Drusvyatskiy, Stochastic Model-Based Minimization of Weakly Convex Functions, arXiv:1803.06523v3, p. 15, Lemma 3.3 (proof p. 16)

import Mathlib
import Definitions.Def_StochModelWC_ProxSubgrad_Basic
import Definitions.Def_StochModelWC_ProxSubgrad_AssumptionA

open MeasureTheory Filter Topology

namespace StochModelWC.ProxSubgrad

/-- Lemma 3.3 (p. 15), one step of Algorithm 3.1 with the current iterate `x` held fixed:
`E_ξ ‖prox_{α r}(x − α G(x, ξ)) − x̂‖² ≤ ‖x − x̂‖² + 4 α² L² − 2 α (ρ̄ − ρ) ‖x − x̂‖²`,
where `x̂ = prox_{φ/ρ̄}(x)`. -/
theorem lemma_3_3 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U D : Set (EuclideanSpace ℝ (Fin d))) (f r : EuclideanSpace ℝ (Fin d) → ℝ)
    (G : EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d)) (ρ L : ℝ)
    (hD : D.Nonempty) (hr_cl : StochModelWC.ModelBased.IsClosedFn D r) (hr_cvx : ConvexOn ℝ D r)
    (hf : StochModelWC.ModelBased.IsWeaklyConvexOn Set.univ ρ f) (hA : AssumptionA P U D f G L)
    (prox : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hprox : ∀ a : ℝ, 0 < a → ∀ z, StochModelWC.ModelBased.IsProxPt D r a z (prox a z))
    (ρbar α : ℝ) (hρbar : ρ < ρbar) (hρbar2 : ρbar ≤ 2 * ρ) (hα0 : 0 < α) (hα1 : α ≤ 1 / ρbar)
    (x xhat : EuclideanSpace ℝ (Fin d)) (hx : x ∈ D)
    (hxhat : StochModelWC.ModelBased.IsProxPt D (fun y => f y + r y) (1 / ρbar) x xhat) :
    Integrable (fun ξ => ‖prox α (x - α • G x ξ) - xhat‖ ^ 2) P ∧
    ∫ ξ, ‖prox α (x - α • G x ξ) - xhat‖ ^ 2 ∂P ≤
      ‖x - xhat‖ ^ 2 + 4 * α ^ 2 * L ^ 2 - 2 * α * (ρbar - ρ) * ‖x - xhat‖ ^ 2 := by sorry

end StochModelWC.ProxSubgrad
