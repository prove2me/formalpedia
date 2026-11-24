-- Prove2me | Theorems.Thm_SSLSpectralEmbedding_linear_probe_minimum_loss
-- name    : SSLSpectralEmbedding.linear_probe_minimum_loss
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:26:34.083063+00:00
-- url     : https://prove2.me/theorems/ab0eeab9-978d-4726-a84a-641a047d4c5e
-- title:
--   Theorem 8: necessary and sufficient condition for a representation to solve a task linearly
-- statement:
--   Let $Y\in\mathbb{R}^{N\times C}$ be a task and $Z\in\mathbb{R}^{N\times K}$ a representation, and let $\widehat U_z$ be the left singular vectors of $Z$ with nonzero singular values, i.e. an orthonormal basis $\widehat U_z\in\mathbb{R}^{N\times r}$ of the column space of $Z$. With $\mathcal L(W)=\frac12\|Y-ZW\|_F^2$, the minimum is attained and
--
--   $$\min_{W\in\mathbb{R}^{K\times C}}\mathcal L(W)=\frac12\|Y\|_F^2-\frac12\|\widehat U_z^\top U_y\Sigma_y\|_F^2,$$
--
--   where $Y=U_y\Sigma_yV_y^\top$. This minimum is $0$ if and only if the columns of $\widehat U_z$ span the columns of $\widehat U_y$, the left singular vectors of $Y$ with nonzero singular values.
--
--   **Formalization Note** $\widehat U_z$ is taken to be any matrix with orthonormal columns and the same column space as $Z$. The right-hand side does not depend on the choice. Because $U_y\Sigma_y=YV_y$ with $V_y$ orthogonal, $\|\widehat U_z^\top U_y\Sigma_y\|_F=\|\widehat U_z^\top Y\|_F$, and the latter is used. The span of $\widehat U_y$ is the column space of $Y$, so the span condition is stated as inclusion of column spaces.
-- source:
--   Balestriero and LeCun, Contrastive and Non-Contrastive Self-Supervised Learning Recover Global and Local Spectral Embedding Methods, arXiv:2205.11508v3 (NeurIPS 2022), Section 6.2, Theorem 8, eq. (22), p. 16; proof in Appendix A.2-A.4, p. 24

import Mathlib
import Definitions.Def_SSLSpectralEmbedding_Basic

open Matrix

namespace SSLSpectralEmbedding

theorem linear_probe_minimum_loss {N K C r : ℕ} (Y : Matrix (Fin N) (Fin C) ℝ)
    (Z : Matrix (Fin N) (Fin K) ℝ) (U : Matrix (Fin N) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (hUZ : LinearMap.range (Matrix.toLin' U) = LinearMap.range (Matrix.toLin' Z)) :
    IsLeast (Set.range fun W : Matrix (Fin K) (Fin C) ℝ => lsLoss Y Z W)
      ((1 / 2) * frobSq Y - (1 / 2) * frobSq (Uᵀ * Y)) ∧
    ((1 / 2) * frobSq Y - (1 / 2) * frobSq (Uᵀ * Y) = 0 ↔
      LinearMap.range (Matrix.toLin' Y) ≤ LinearMap.range (Matrix.toLin' U)) := by sorry

end SSLSpectralEmbedding
