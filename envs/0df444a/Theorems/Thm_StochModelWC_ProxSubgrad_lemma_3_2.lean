-- Prove2me | Theorems.Thm_StochModelWC_ProxSubgrad_lemma_3_2
-- name    : StochModelWC.ProxSubgrad.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:43:24.316993+00:00
-- url     : https://prove2.me/theorems/f1048d93-f772-45ae-82a0-7979d8d06b24
-- title:
--   Lemma 3.2 — x̂ₜ is a proximal point of r
-- statement:
--   Let $r$ be closed and convex with nonempty domain $D$, $f$ be $\rho$-weakly convex, $\varphi = f + r$, and $\bar\rho > \rho$. Let $x \in D$, let $\hat x = \operatorname{prox}_{\varphi/\bar\rho}(x)$, and let $\hat v$ be a vector with $\hat v \in \partial f(\hat x)$ and $\bar\rho(x - \hat x) - \hat v \in \partial r(\hat x)$ (the vector produced in §3.2). Then for every $\alpha > 0$,
--   $$\hat x = \operatorname{prox}_{\alpha r}\big(\alpha\bar\rho\, x - \alpha\hat v + (1 - \alpha\bar\rho)\,\hat x\big).$$
--
--   The lemma realizes the proximal point of $\varphi$ as a proximal point of $r$ alone at a shifted argument, which allows the 1-Lipschitz property of $\operatorname{prox}_{\alpha r}$ to compare the iterate $x_{t+1}$ with $\hat x_t$.
--
--   **Formalization Note.** The conclusion says that $\hat x$ is a minimizer of $y \mapsto r(y) + \frac{1}{2\alpha}\|y - z\|^2$ over $D$ at the displayed $z$; for convex $r$ that minimizer is unique, so this is the stated equality.
-- source:
--   Davis–Drusvyatskiy, Stochastic Model-Based Minimization of Weakly Convex Functions, arXiv:1803.06523v3, p. 15, Lemma 3.2

import Mathlib
import Definitions.Def_StochModelWC_ProxSubgrad_Basic

open MeasureTheory Filter Topology

namespace StochModelWC.ProxSubgrad

/-- Lemma 3.2 (p. 15): with `x̂ = prox_{φ/ρ̄}(x)` and `v̂` as in the preceding paragraph,
`x̂ = prox_{α r}(α ρ̄ x − α v̂ + (1 − α ρ̄) x̂)`. -/
theorem lemma_3_2 {d : ℕ} (D : Set (EuclideanSpace ℝ (Fin d)))
    (f r : EuclideanSpace ℝ (Fin d) → ℝ) (ρ ρbar α : ℝ)
    (hD : D.Nonempty) (hr_cl : StochModelWC.ModelBased.IsClosedFn D r) (hr_cvx : ConvexOn ℝ D r)
    (hf : StochModelWC.ModelBased.IsWeaklyConvexOn Set.univ ρ f) (hρbar : ρ < ρbar) (hα : 0 < α)
    (x xhat vhat : EuclideanSpace ℝ (Fin d)) (hx : x ∈ D)
    (hxhat : StochModelWC.ModelBased.IsProxPt D (fun y => f y + r y) (1 / ρbar) x xhat)
    (hvhat : vhat ∈ frechetSubdiff Set.univ f xhat)
    (hvhat_r : ρbar • (x - xhat) - vhat ∈ frechetSubdiff D r xhat) :
    StochModelWC.ModelBased.IsProxPt D r α ((α * ρbar) • x - α • vhat + (1 - α * ρbar) • xhat) xhat := by sorry

end StochModelWC.ProxSubgrad
