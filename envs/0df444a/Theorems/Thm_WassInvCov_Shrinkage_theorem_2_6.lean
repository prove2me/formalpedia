-- Prove2me | Theorems.Thm_WassInvCov_Shrinkage_theorem_2_6
-- name    : WassInvCov.Shrinkage.theorem_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:30:38.539274+00:00
-- url     : https://prove2.me/theorems/99029b9f-265b-4e3e-9a49-59d0eb8b9676
-- title:
--   Theorem 2.6, p. 7 — problem (5) equals the convex program (6), and its value 𝒥(Σ̂) is continuous on 𝕊^p_+
-- statement:
--   Let $\mathcal X\subseteq\mathbb S^p_{++}$ be any set of admissible precision matrices and fix $\rho>0$. For $\widehat\Sigma\in\mathbb S^p_+$ let $\mathcal J(\widehat\Sigma)=\inf_{X\in\mathcal X}\{-\log\det X+g(\widehat\Sigma,X)\}$ be the optimal value of the distributionally robust estimation problem (5), with $g$ the worst-case expectation (7). Then:
--   1. for every $\widehat\Sigma\succeq0$,
--   $$\mathcal J(\widehat\Sigma)=\inf_{X,\gamma}\Big\{-\log\det X+\gamma\big(\rho^2-\operatorname{Tr}[\widehat\Sigma]\big)+\gamma^2\big\langle(\gamma I-X)^{-1},\widehat\Sigma\big\rangle:\ \gamma I\succ X\succ0,\ X\in\mathcal X\Big\};\tag{6}$$
--   2. the optimal value function $\mathcal J$ is continuous on $\mathbb S^p_+$.
--
--   The theorem turns the robust problem over a nonconvex set of distributions into a convex program in $(X,\gamma)$; its continuity statement is what extends Theorem 3.1 to singular sample covariance matrices.
--
--   **Formalization Note** $\mathcal X$ is an arbitrary subset of $\mathbb S^p_{++}$, as on the page (Theorem 3.1 later takes $\mathcal X=\mathbb S^p_{++}$). Both optimal values are infima in the extended reals; continuity is with respect to the entrywise topology on $p\times p$ matrices, restricted to $\mathbb S^p_+$.
-- source:
--   Nguyen, Kuhn & Mohajerin Esfahani, Distributionally Robust Inverse Covariance Estimation, arXiv:1805.07194v1, p. 7, Theorem 2.6, (5), (6)

import Mathlib
import Definitions.Def_WassInvCov_Shrinkage_Setting

open MeasureTheory ProbabilityTheory Matrix

namespace WassInvCov.Shrinkage

/-- Theorem 2.6, p. 7 (arXiv:1805.07194v1): for any set `𝒳 ⊆ 𝕊^p_{++}` of admissible precision
matrices and fixed `ρ > 0`, for every `Σ̂ ⪰ 0` the optimal value `𝒥(Σ̂)` of (5) equals that of the
convex program (6), and `𝒥` is continuous on `𝕊^p_+`. -/
theorem theorem_2_6 {p : ℕ} (𝒳 : Set (Matrix (Fin p) (Fin p) ℝ)) (h𝒳 : ∀ X ∈ 𝒳, X.PosDef)
    (ρ : ℝ) (hρ : 0 < ρ) :
    (∀ Sh : Matrix (Fin p) (Fin p) ℝ, Sh.PosSemidef → J 𝒳 ρ Sh = value6 𝒳 ρ Sh) ∧
    ContinuousOn (J 𝒳 ρ) {Sh | Sh.PosSemidef} := by sorry

end WassInvCov.Shrinkage
