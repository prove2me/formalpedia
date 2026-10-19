-- Prove2me | Theorems.Thm_WassInvCov_Shrinkage_phi16b_unique_root
-- name    : WassInvCov.Shrinkage.phi16b_unique_root
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:30:38.141089+00:00
-- url     : https://prove2.me/theorems/c0875344-8596-4fc0-b199-16a282d8fbd5
-- title:
--   Proof of Theorem 3.1, p. 12 — equation (16b) has a unique solution in ℝ_+, and it is positive
-- statement:
--   Let $p\ge1$, $\rho>0$ and $\lambda_1,\dots,\lambda_p\ge0$, and let
--
--   $$\varphi(\gamma)=\Big(\rho^2-\frac12\sum_{i=1}^p\lambda_i\Big)\gamma-p+\frac12\sum_{i=1}^p\sqrt{\lambda_i^2\gamma^2+4\lambda_i\gamma}$$
--
--   be the left-hand side of (16b). Then the equation $\varphi(\gamma)=0$ has exactly one solution $\gamma^\star\in[0,\infty)$, and $\gamma^\star>0$.
--
--   This is the first step of the proof of Theorem 3.1: it makes the parameter $\gamma^\star$ of the shrinkage formula (16a) well defined.
--
--   **Formalization Note** The hypothesis $p\ge1$ is added: for $p=0$ the equation reads $\rho^2\gamma=0$, whose only solution $\gamma=0$ is not positive. The page says "a unique solution in $\mathbb R_+$" and, in the theorem, "the unique positive solution"; both are stated.
-- source:
--   Nguyen, Kuhn & Mohajerin Esfahani, Distributionally Robust Inverse Covariance Estimation, arXiv:1805.07194v1, p. 12, proof of Theorem 3.1, first paragraph, (16b)

import Mathlib
import Definitions.Def_WassInvCov_Shrinkage_Setting

open MeasureTheory ProbabilityTheory Matrix

namespace WassInvCov.Shrinkage

/-- Proof of Theorem 3.1, p. 12, first paragraph (arXiv:1805.07194v1): for `p ≥ 1`, `ρ > 0` and
`λᵢ ≥ 0`, the algebraic equation (16b) has a unique solution in `ℝ_+ = [0, ∞)`, and that solution is
positive. -/
theorem phi16b_unique_root {p : ℕ} (hp : 0 < p) (ρ : ℝ) (hρ : 0 < ρ) (lam : Fin p → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) :
    (∃! γ : ℝ, 0 ≤ γ ∧ phi16b ρ lam γ = 0) ∧
    ∀ γ : ℝ, 0 ≤ γ → phi16b ρ lam γ = 0 → 0 < γ := by sorry

end WassInvCov.Shrinkage
