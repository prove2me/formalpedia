-- Prove2me | Theorems.Thm_StochModelWC_ModelBased_lemma_2_2
-- name    : StochModelWC.ModelBased.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:50:20.45832+00:00
-- url     : https://prove2.me/theorems/50eb036f-8b40-43c2-bc69-6e85e7902ae0
-- title:
--   Lemma 2.2 — the Moreau envelope of a ρ-weakly convex function is C¹ with ∇φ_λ(x) = λ⁻¹(x − prox_{λφ}(x))
-- statement:
--   Let $\varphi:\mathbb R^d\to\mathbb R\cup\{\infty\}$ be closed, proper (nonempty domain $D$) and $\rho$-weakly convex with $\rho>0$, and let $\lambda\in(0,\rho^{-1})$. Then:
--
--   1. for every $x$ the proximal point $\operatorname{prox}_{\lambda\varphi}(x)=\operatorname*{argmin}_y\{\varphi(y)+\frac{1}{2\lambda}\|y-x\|^2\}$ exists and is unique;
--   2. the Moreau envelope $\varphi_\lambda$ is $C^1$-smooth;
--   3. its gradient is
--   $$\nabla\varphi_\lambda(x)=\lambda^{-1}\big(x-\operatorname{prox}_{\lambda\varphi}(x)\big).$$
--
--   This is the fact that turns $\|\nabla\varphi_{1/\bar\rho}(x)\|$ into a usable stationarity measure: it equals $\bar\rho\,\|x-\hat x\|$, the scaled distance to the proximal point, which is how the paper's convergence estimates are converted into gradient bounds.
--
--   **Formalization Note** "Closed" and "proper" are implicit in the paper's statement (the lemma fails without closedness) and are hypotheses here. The convex case is covered since a convex function is $\rho$-weakly convex for every $\rho>0$.
-- source:
--   Davis–Drusvyatskiy, Stochastic Model-Based Minimization of Weakly Convex Functions, arXiv:1803.06523v3, p. 11, Lemma 2.2 (with (2.6))

import Mathlib
import Definitions.Def_StochModelWC_ModelBased_Basic

open MeasureTheory Filter Topology

namespace StochModelWC.ModelBased

/-- Lemma 2.2 (p. 11): for a closed, proper, `ρ`-weakly convex `φ : ℝ^d → ℝ ∪ {∞}` (encoded by `(D, φ)`) and
`lam ∈ (0, ρ⁻¹)`, the proximal map is single-valued, the Moreau envelope `φ_lam` is `C¹`, and
`∇φ_lam(x) = lam⁻¹ (x − prox_{lam φ}(x))`. -/
theorem lemma_2_2 {d : ℕ} (D : Set (EuclideanSpace ℝ (Fin d))) (φ : EuclideanSpace ℝ (Fin d) → ℝ) (ρ lam : ℝ)
    (hD : D.Nonempty) (hcl : IsClosedFn D φ) (hwc : IsWeaklyConvexOn D ρ φ)
    (hρ : 0 < ρ) (hlam : 0 < lam) (hlamρ : lam < ρ⁻¹) :
    (∀ x, ∃! p, IsProxPt D φ lam x p) ∧
      ContDiff ℝ 1 (moreauEnv D φ lam) ∧
      ∀ x p, IsProxPt D φ lam x p → HasGradientAt (moreauEnv D φ lam) (lam⁻¹ • (x - p)) x := by sorry

end StochModelWC.ModelBased
