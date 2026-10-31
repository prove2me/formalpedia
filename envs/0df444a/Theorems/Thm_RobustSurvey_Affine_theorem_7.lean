-- Prove2me | Theorems.Thm_RobustSurvey_Affine_theorem_7
-- name    : RobustSurvey.Affine.theorem_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:03:39.691754+00:00
-- url     : https://prove2.me/theorems/43a6c693-56a2-4557-9714-a8c638c53b8c
-- title:
--   Theorem 7 — tightness of the semidefinite approximation for affine adaptability
-- statement:
--   Let $m,n_1,n_2,L$ be arbitrary finite dimensions and $K\ge1$. Let $c,b,A_1^{(0)},A_2^{(0)},A_1^{(l)},A_2^{(l)}$ be arbitrary real two-stage data of the indicated dimensions, with $A_j(u)=A_j^{(0)}+\sum_lu_lA_j^{(l)}$. Let $S_1,\ldots,S_K\succeq0$ be real symmetric matrices and $\rho>0$. Use the full policy tuple $\chi=(x_1,q,Q)$ and $U_\rho=\{u:u^T(\rho^{-2}S_k)u\le1\ \forall k\}$. The coefficients $\alpha,\beta,\Gamma$ are the literal printed formulas preceding (4.13), and $M_i$ is the explicit block matrix of (4.14).
--
--   Assume $r=\sum_k\operatorname{rank}_{\mathbb R}(S_k)>0$ and put $\gamma=\sqrt{2\ln(6r)}$. Let $X_t$ consist of the complete policy tuples satisfying the original robust constraints at radius $t$, and let $X_\rho^{\mathrm{approx}}$ consist of tuples admitting the nonnegative multipliers in the printed SDP. Then
--   $$X_{\gamma\rho}\subseteq X_\rho^{\mathrm{approx}}\subseteq X_\rho.$$
--   Both inclusions use exactly the same data and matrices $S_k$, changing only the radius in the first set. The constants 2 and 6, every policy coefficient, the continuum of uncertainty, and uncertain recourse are retained. This is a comparison of feasible sets, with no optimality or attainment hypothesis. It preserves the literal printed assertion, whose right inclusion is contradicted by the source-coefficient counterexample I1.
--
--   Differences from the source:
--   - encoding: finite real coordinate vectors and matrices indexed from 1 → Fin coordinates indexed from 0, with the constant terms stored separately and the SDP scalar coordinate last; reason: a coordinate relabeling preserves every finite-dimensional instance and the full policy tuple
--   - encoding: rho^(-2) and the real logarithm ln(6 sum_k Rank(S_k)) → rho > 0 and positive rank sum, using natural matrix ranks coerced to real numbers; reason: exclude undefined displayed inputs; rank positivity already implies K > 0 and L > 0
--   - reading: lambda_k in the upper-left block, lambda_k^(i) in the other constraints of (4.14) → the same row-specific lambda^(i) in both blocks; reason: the row index i labels each PSD constraint and its nonnegative multiplier vector
-- source:
--   Bertsimas, Brown and Caramanis, Theory and Applications of Robust Optimization, held PDF marked arXiv:1010.5445v1 (2010), https://arxiv.org/abs/1010.5445v1; SHA-256 25714e004b9b868fcb48997d3364800e379cd1be5f8b027ca6f50ee08f25ae50; anomalous revised-version date November 26, 2024; Theorem 7 and gamma display, printed p. 26 / PDF p. 27.

import Definitions.Def_RobustSurvey_Affine_SDP

namespace RobustSurvey.Affine

theorem theorem_7 {m n₁ n₂ L K : ℕ} (D : Data m n₁ n₂ L)
    (E : Ellipsoids L K) (hrank : 0 < E.rankSum) (ρ : ℝ) (hρ : 0 < ρ) :
    aarcFeasible D E (E.gamma * ρ) ⊆ approxFeasible D E ρ ∧
      approxFeasible D E ρ ⊆ aarcFeasible D E ρ := by sorry

end RobustSurvey.Affine
