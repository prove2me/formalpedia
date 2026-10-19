-- Prove2me | Theorems.Thm_WassInvCov_Shrinkage_proposition_2_8
-- name    : WassInvCov.Shrinkage.proposition_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:30:38.090773+00:00
-- url     : https://prove2.me/theorems/9304bcbe-6bd5-4169-979a-61770256cf33
-- title:
--   Proposition 2.8, p. 7 — the worst-case expectation g equals the one-dimensional program (8) and is continuous on 𝕊^p_+ × 𝕊^p_{++}
-- statement:
--   Fix $\rho>0$. For $\widehat\Sigma\in\mathbb S^p_+$ and $X\in\mathbb S^p_{++}$ let $g(\widehat\Sigma,X)=\sup_{\mathbb Q\in\mathcal P^0_\rho}\mathbb E^{\mathbb Q}[\langle\xi\xi^\top,X\rangle]$ be the worst-case expectation (7) over the centred normal distributions within type-2 Wasserstein distance $\rho$ of $\mathcal N(0,\widehat\Sigma)$. Then:
--   1. for every $\widehat\Sigma\succeq0$ and $X\succ0$,
--   $$g(\widehat\Sigma,X)=\inf_{\gamma:\ \gamma I\succ X}\ \gamma\big(\rho^2-\operatorname{Tr}[\widehat\Sigma]\big)+\gamma^2\big\langle(\gamma I-X)^{-1},\widehat\Sigma\big\rangle,\tag{8}$$
--   2. the map $(\widehat\Sigma,X)\mapsto g(\widehat\Sigma,X)$ is continuous on $\mathbb S^p_+\times\mathbb S^p_{++}$.
--
--   The proposition replaces an optimization over distributions by a scalar convex program, which is what makes problem (5) tractable; its continuity statement is used to extend Theorem 3.1 from positive definite to singular $\widehat\Sigma$.
--
--   **Formalization Note** Both sides of (8) are computed in the extended reals; the constraint $\gamma I\succ X$ sits in the index of the infimum, so the matrix inverse is only evaluated where it exists. Continuity is for the product topology on pairs of $p\times p$ real matrices, restricted to $\mathbb S^p_+\times\mathbb S^p_{++}$, with values in the extended reals (all values on that set are finite). The published Open theorem `WassMMSE.Sandwich.proposition_A_4_i` gives the covariance-level duality for a symmetric matrix and $\rho\ge0$, and is included in this mission for reuse.
-- source:
--   Nguyen, Kuhn & Mohajerin Esfahani, Distributionally Robust Inverse Covariance Estimation, arXiv:1805.07194v1, p. 7, Proposition 2.8, (8)

import Mathlib
import Definitions.Def_WassInvCov_Shrinkage_Setting

open MeasureTheory ProbabilityTheory Matrix

namespace WassInvCov.Shrinkage

/-- Proposition 2.8, p. 7 (arXiv:1805.07194v1): for fixed `ρ > 0`, for every `Σ̂ ⪰ 0` and `X ≻ 0` the
worst-case expectation `g(Σ̂, X)` of (7) equals the optimal value of the semidefinite program (8),
and `g` is continuous on `𝕊^p_+ × 𝕊^p_{++}`. -/
theorem proposition_2_8 {p : ℕ} (ρ : ℝ) (hρ : 0 < ρ) :
    (∀ Sh X : Matrix (Fin p) (Fin p) ℝ, Sh.PosSemidef → X.PosDef →
      worstCaseExp ρ Sh X = sdp8 ρ Sh X) ∧
    ContinuousOn (fun z : Matrix (Fin p) (Fin p) ℝ × Matrix (Fin p) (Fin p) ℝ =>
        worstCaseExp ρ z.1 z.2)
      {z | z.1.PosSemidef ∧ z.2.PosDef} := by sorry

end WassInvCov.Shrinkage
