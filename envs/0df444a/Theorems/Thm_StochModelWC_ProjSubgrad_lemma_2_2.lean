-- Prove2me | Theorems.Thm_StochModelWC_ProjSubgrad_lemma_2_2
-- name    : StochModelWC.ProjSubgrad.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:35:51.504984+00:00
-- url     : https://prove2.me/theorems/957e27f9-42bd-4a5b-b1d7-61e781cd7fe9
-- title:
--   Lemma 2.2 — the Moreau envelope of a weakly convex function is C¹
-- statement:
--   Let $\varphi : \mathbb R^d \to \mathbb R \cup \{+\infty\}$ be closed, with nonempty domain, and $\rho$-weakly convex for some $\rho > 0$. Then for every $\lambda \in (0, \rho^{-1})$:
--
--   1. for every $x$ the proximal point $\operatorname{prox}_{\lambda\varphi}(x)$ exists and is unique;
--   2. the Moreau envelope $\varphi_\lambda$ is $C^1$-smooth;
--   3. its gradient is
--   $$\nabla\varphi_\lambda(x) = \lambda^{-1}\big(x - \operatorname{prox}_{\lambda\varphi}(x)\big).$$
--
--   The norm $\|\nabla\varphi_\lambda(x)\|$ is the stationarity measure in which all convergence guarantees of the paper are stated; the gradient formula converts the distance $\|x - \hat x\|$ to the proximal point into it.
--
--   **Formalization Note.** "Closed" and "proper" (nonempty domain) are implicit on the page and are stated as hypotheses; the lemma is false without closedness. Item 1 makes explicit the well-posedness of $\operatorname{prox}_{\lambda\varphi}$ that the formula presupposes.
-- source:
--   Davis–Drusvyatskiy, Stochastic Model-Based Minimization of Weakly Convex Functions, arXiv:1803.06523v3, p. 11, Lemma 2.2

import Mathlib
import Definitions.Def_StochModelWC_ProjSubgrad_Basic

open MeasureTheory Filter Topology

namespace StochModelWC.ProjSubgrad

/-- Lemma 2.2 (p. 11): for a closed proper `ρ`-weakly convex `φ` (encoded by `(D, φ)`) and `λ ∈ (0, ρ⁻¹)`,
the proximal point is unique, the Moreau envelope `φ_λ` is `C¹`, and `∇φ_λ(x) = λ⁻¹(x − prox_{λφ}(x))`. -/
theorem lemma_2_2 {d : ℕ} (D : Set (EuclideanSpace ℝ (Fin d))) (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (ρ lam : ℝ) (hD : D.Nonempty) (hcl : IsClosedFn D φ) (hwc : IsWeaklyConvexOn D ρ φ)
    (hρ : 0 < ρ) (hlam : 0 < lam) (hlam' : lam < ρ⁻¹) :
    (∀ x, ∃! p, IsProxPt D φ lam x p) ∧
    ContDiff ℝ 1 (moreauEnv D φ lam) ∧
    ∀ x p, IsProxPt D φ lam x p → HasGradientAt (moreauEnv D φ lam) (lam⁻¹ • (x - p)) x := by sorry

end StochModelWC.ProjSubgrad
