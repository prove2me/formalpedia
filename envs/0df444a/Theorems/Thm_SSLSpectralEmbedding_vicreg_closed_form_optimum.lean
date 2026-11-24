-- Prove2me | Theorems.Thm_SSLSpectralEmbedding_vicreg_closed_form_optimum
-- name    : SSLSpectralEmbedding.vicreg_closed_form_optimum
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:24:35.454433+00:00
-- url     : https://prove2.me/theorems/1f4afae6-6ef6-4cf8-b94b-17326e4a5a3c
-- title:
--   Theorem 1 (as proved): closed-form global minimiser and minimal value of VICReg
-- statement:
--   Let $G$ be a relation matrix on $N$ samples, $1\le K\le N$ (the case $K=0$ is trivial), $\alpha>0$ and $\gamma\ge0$. Consider the VICReg loss with $\beta=\alpha$ and the squared variance term,
--
--   $$\mathcal L_{\rm VIC}(Z)=\alpha\sum_{k}(1-\operatorname{Cov}(Z)_{k,k})^2+\alpha\sum_k\sum_{j\ne k}\operatorname{Cov}(Z)_{k,j}^2+\frac{\gamma}{N}\sum_{i,j}G_{i,j}\|Z_{i,.}-Z_{j,.}\|_2^2,$$
--
--   where $\operatorname{Cov}(Z)=\frac1NZ^\top(I-\frac1N\mathbf 1\mathbf 1^\top)Z$. Let
--
--   $$I-\tfrac1N\mathbf 1\mathbf 1^\top-\tfrac{\gamma}{\alpha}(D-G)=P\operatorname{diag}(\lambda)P^\top$$
--
--   with $P$ orthogonal and $\lambda_1\ge\dots\ge\lambda_N$, and suppose $\lambda_K\ge0$. Then $Z^*_{\alpha,\gamma}=(P(\operatorname{diag}(\lambda)N)^{1/2})_{:,1:K}$, the matrix whose $k$-th column is $\sqrt{N\lambda_k}$ times the $k$-th column of $P$, is a global minimiser of $\mathcal L_{\rm VIC}$ over $\mathbb{R}^{N\times K}$, and
--
--   $$\min_{Z\in\mathbb{R}^{N\times K}}\mathcal L_{\rm VIC}(Z)=\alpha\Big(K-\sum_{k=1}^K\lambda_k^2\Big).$$
--
--   **Formalization Note** The paper states the result with no condition on $\lambda$. The hypothesis $\lambda_K\ge0$ is the condition under which $(\operatorname{diag}(\lambda)N)^{1/2}$ is real. Without it the value formula is false: for the complete graph with $N=6$, $K=2$, $\alpha=\gamma=1$ it gives $-23$, while the loss is nonnegative. The paper's further claim that any $K$ of the $N$ columns of $P(\operatorname{diag}(\lambda)N)^{1/2}$ give a local minimum is false and is not included.
-- source:
--   Balestriero and LeCun, Contrastive and Non-Contrastive Self-Supervised Learning Recover Global and Local Spectral Embedding Methods, arXiv:2205.11508v3 (NeurIPS 2022), Section 3.1, Theorem 1, eq. (8), pp. 6-7; proof in Appendix A.7, p. 25

import Mathlib
import Definitions.Def_SSLSpectralEmbedding_Basic

open Matrix

namespace SSLSpectralEmbedding

theorem vicreg_closed_form_optimum {N K : ℕ} (hKN : K ≤ N) (α γ : ℝ) (hα : 0 < α) (hγ : 0 ≤ γ)
    (G : Matrix (Fin N) (Fin N) ℝ) (hG : IsRelationMatrix G)
    (P : Matrix (Fin N) (Fin N) ℝ) (lam : Fin N → ℝ) (hP : IsDescEigendecomp (vicMat α γ G) P lam)
    (hlam : ∀ k : Fin K, 0 ≤ lam (Fin.castLE hKN k)) :
    (∀ Z : Matrix (Fin N) (Fin K) ℝ,
      vicLossSq α α γ G (vicOpt P lam hKN) ≤ vicLossSq α α γ G Z) ∧
    vicLossSq α α γ G (vicOpt P lam hKN) = α * (K - ∑ k : Fin K, lam (Fin.castLE hKN k) ^ 2) := by sorry

end SSLSpectralEmbedding
