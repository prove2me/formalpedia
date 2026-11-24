-- Prove2me | Theorems.Thm_SSLSpectralEmbedding_linear_vicreg_optimal_weights
-- name    : SSLSpectralEmbedding.linear_vicreg_optimal_weights
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:25:39.311663+00:00
-- url     : https://prove2.me/theorems/4c6c8cba-b45b-47af-a138-671ec324870e
-- title:
--   Eq. (12) (as proved, $K = D$): optimal weights of linear VICReg
-- statement:
--   Let $G$ be a relation matrix with Laplacian $L$, let $X\in\mathbb{R}^{N\times D}$ have invertible covariance $A=\operatorname{Cov}(X)$, let $\alpha>0$, $\gamma\ge0$, and consider the linear VICReg model $Z=XW$, $W\in\mathbb{R}^{D\times K}$, with $K=D$, trained with the squared-variance VICReg loss with $\beta=\alpha$. Let
--
--   $$B=\operatorname{Cov}(X)-\frac{\gamma}{\alpha N}X^\top LX$$
--
--   be positive semidefinite, with positive semidefinite square root $B^{1/2}$. Then
--
--   $$W^*=\operatorname{Cov}(X)^{-1}B^{1/2}$$
--
--   minimises $\mathcal L_{\rm vic}(XW)$ over all $W\in\mathbb{R}^{D\times D}$.
--
--   **Formalization Note** Eq. (12) takes the first $K$ columns of $W^*$ for $K\le D$. The proof in Appendix A.9 treats only $K=D$, and the statement is restricted to that case. For $K<D$ the proof's claim that every choice of $K$ columns gives the same loss is unsupported. Positive semidefiniteness of $B$ is the implicit condition for $B^{1/2}$ to be real. The square root is any positive semidefinite $R$ with $R^2=B$, which is unique.
-- source:
--   Balestriero and LeCun, Contrastive and Non-Contrastive Self-Supervised Learning Recover Global and Local Spectral Embedding Methods, arXiv:2205.11508v3 (NeurIPS 2022), Section 3.3, eq. (12), p. 10; proof in Appendix A.9, p. 26

import Mathlib
import Definitions.Def_SSLSpectralEmbedding_Basic

open Matrix

namespace SSLSpectralEmbedding

theorem linear_vicreg_optimal_weights {N D : ℕ} (α γ : ℝ) (hα : 0 < α) (hγ : 0 ≤ γ)
    (G : Matrix (Fin N) (Fin N) ℝ) (hG : IsRelationMatrix G) (X : Matrix (Fin N) (Fin D) ℝ)
    (hX : (cov X).det ≠ 0) (hB : (linB α γ G X).PosSemidef)
    (R : Matrix (Fin D) (Fin D) ℝ) (hR : R.PosSemidef) (hRB : R * R = linB α γ G X) :
    ∀ W : Matrix (Fin D) (Fin D) ℝ,
      vicLossSq α α γ G (X * ((cov X)⁻¹ * R)) ≤ vicLossSq α α γ G (X * W) := by sorry

end SSLSpectralEmbedding
