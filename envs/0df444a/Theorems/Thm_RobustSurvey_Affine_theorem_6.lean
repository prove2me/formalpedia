-- Prove2me | Theorems.Thm_RobustSurvey_Affine_theorem_6
-- name    : RobustSurvey.Affine.theorem_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:03:49.718848+00:00
-- url     : https://prove2.me/theorems/a01a7c57-3626-47f8-89c8-9cac8460201e
-- title:
--   Theorem 6 — semidefinite inner approximation of the original AARC
-- statement:
--   Let $m,n_1,n_2,L$ be arbitrary finite dimensions and $K\ge1$. Let $c,b,A_1^{(0)},A_2^{(0)},A_1^{(l)},A_2^{(l)}$ be arbitrary real two-stage data of the indicated dimensions, with $A_j(u)=A_j^{(0)}+\sum_lu_lA_j^{(l)}$. Let $S_1,\ldots,S_K\succeq0$ be real symmetric matrices and $\rho>0$. Use the full policy tuple $\chi=(x_1,q,Q)$ and $U_\rho=\{u:u^T(\rho^{-2}S_k)u\le1\ \forall k\}$. The coefficients $\alpha,\beta,\Gamma$ are the literal printed formulas preceding (4.13), and $M_i$ is the explicit block matrix of (4.14).
--
--   Every full tuple $\chi$ and collection of row multipliers $\lambda$ satisfying $\lambda_k^{(i)}\ge0$ and $M_i(\chi,\lambda,\rho)\succeq0$ for all rows gives
--   $$A_1(u)x_1+A_2(u)(Qu+q)\le b\quad\text{for every }u\in U_\rho,$$
--   and the SDP objective at $(\chi,\lambda)$ equals the AARC objective at $\chi$, namely $c^Tx_1$. Thus the displayed SDP is an inner approximation with the same minimization objective. No existence of an optimum is claimed. Singular ellipsoid matrices and uncertainty-dependent recourse remain allowed. This states the printed assertion; the coefficient error affecting it is recorded in I1.
--
--   Differences from the source:
--   - encoding: finite real coordinate vectors and matrices indexed from 1 → Fin coordinates indexed from 0, with the constant terms stored separately and the SDP scalar coordinate last; reason: a coordinate relabeling preserves every finite-dimensional instance and the full policy tuple
--   - encoding: rho controls the size through rho^(-2) → rho > 0; reason: positive radius is the size convention and excludes the undefined reciprocal at zero
--   - reading: lambda_k in the upper-left block, lambda_k^(i) in the other constraints of (4.14) → the same row-specific lambda^(i) in both blocks; reason: the row index i labels each PSD constraint and its nonnegative multiplier vector
--   - reading: Theorem 6 says the original AARC can be approximated by (4.14) → every feasible SDP certificate yields an original feasible policy with the same objective; reason: the inner-approximation meaning is specified by the right inclusion of the immediately following Theorem 7
-- source:
--   Bertsimas, Brown and Caramanis, Theory and Applications of Robust Optimization, held PDF marked arXiv:1010.5445v1 (2010), https://arxiv.org/abs/1010.5445v1; SHA-256 25714e004b9b868fcb48997d3364800e379cd1be5f8b027ca6f50ee08f25ae50; anomalous revised-version date November 26, 2024; Theorem 6, (4.14), printed pp. 25–26 / PDF pp. 26–27.

import Definitions.Def_RobustSurvey_Affine_SDP

namespace RobustSurvey.Affine

theorem theorem_6 {m n₁ n₂ L K : ℕ} (D : Data m n₁ n₂ L)
    (E : Ellipsoids L K) (hK : 0 < K) (ρ : ℝ) (hρ : 0 < ρ) :
    ∀ (χ : Decision n₁ n₂ L) (lam : Fin m → Fin K → ℝ),
      sdpFeasible D E ρ χ lam →
        χ ∈ aarcFeasible D E ρ ∧ sdpObjective D χ lam = aarcObjective D χ := by sorry

end RobustSurvey.Affine
