-- Prove2me | Theorems.Thm_SSLSpectralEmbedding_lda_eigenvalues_real_nonneg
-- name    : SSLSpectralEmbedding.lda_eigenvalues_real_nonneg
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:27:15.587855+00:00
-- url     : https://prove2.me/theorems/cd712e0f-c942-4afb-8816-afab110f56d1
-- title:
--   Lemma 1: the LDA eigenvalues are real and nonnegative
-- statement:
--   Let $X\in\mathbb{R}^{N\times D}$ be data with class labels $y\in\{1,\dots,C\}^N$. Let $G_{i,j}=1/N_c$ when $y_i=y_j=c$ ($N_c$ the size of class $c$) and $G_{i,j}=0$ otherwise. Let $\Sigma_w=X^\top(I-G)X$ and $\Sigma_b=X^\top GX$ be the within- and between-class scatter matrices, and suppose $\Sigma_w$ is invertible. Let $\Sigma_w^{-1/2}$ be the positive definite square root of $\Sigma_w^{-1}$. Then
--
--   1. $\Sigma_w^{-1}\Sigma_b$ and $\Sigma_w^{-1/2}\Sigma_b\Sigma_w^{-1/2}$ have the same characteristic polynomial, hence the same eigenvalues with multiplicity;
--   2. $\Sigma_w^{-1/2}\Sigma_b\Sigma_w^{-1/2}$ is symmetric;
--   3. every (complex) eigenvalue of $\Sigma_w^{-1}\Sigma_b$ is real and nonnegative.
--
--   The lemma ensures that the generalized eigenvalue problem of LDA, and the division by $1+\lambda_{\rm LDA}$ in Appendix A.16, are well posed.
--
--   **Formalization Note** The square root $\Sigma_w^{-1/2}$ is any positive definite $S$ with $S^2=\Sigma_w^{-1}$, which is unique. Nonnegativity rests on $\Sigma_b$ being positive semidefinite, which the paper does not state: symmetry alone gives real, not nonnegative, eigenvalues.
-- source:
--   Balestriero and LeCun, Contrastive and Non-Contrastive Self-Supervised Learning Recover Global and Local Spectral Embedding Methods, arXiv:2205.11508v3 (NeurIPS 2022), Appendix A.15, Lemma 1, p. 31

import Mathlib
import Definitions.Def_SSLSpectralEmbedding_Basic

open Matrix

namespace SSLSpectralEmbedding

theorem lda_eigenvalues_real_nonneg {N D C : ℕ} (X : Matrix (Fin N) (Fin D) ℝ) (y : Fin N → Fin C)
    (hw : (withinScatter X y).det ≠ 0)
    (S : Matrix (Fin D) (Fin D) ℝ) (hS : S.PosDef) (hSS : S * S = (withinScatter X y)⁻¹) :
    ((withinScatter X y)⁻¹ * betweenScatter X y).charpoly = (S * betweenScatter X y * S).charpoly ∧
    (S * betweenScatter X y * S).IsHermitian ∧
    ∀ μ : ℂ, (((withinScatter X y)⁻¹ * betweenScatter X y).charpoly.map (algebraMap ℝ ℂ)).IsRoot μ →
      μ.im = 0 ∧ 0 ≤ μ.re := by sorry

end SSLSpectralEmbedding
