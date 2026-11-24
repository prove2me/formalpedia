-- Prove2me | Theorems.Thm_SSLSpectralEmbedding_graph_estimate_recovers_simclr
-- name    : SSLSpectralEmbedding.graph_estimate_recovers_simclr
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:26:09.121471+00:00
-- url     : https://prove2.me/theorems/2b979062-237c-4d60-a419-c83d90d5ae22
-- title:
--   Theorem 4 (as proved): entropic graph estimation recovers the SimCLR similarities
-- statement:
--   Let $N\ge2$, $\tau>0$, let $Z\in\mathbb{R}^{N\times K}$ be a representation and $d$ a symmetric dissimilarity on $\mathbb{R}^K$, with $\mathbf D_{i,j}=d(z_i,z_j)$. Let
--
--   $$F(W)=\sum_{i,j}\mathbf D_{i,j}W_{i,j}+\sum_{i\ne j}\tau W_{i,j}(\log W_{i,j}-1).$$
--
--   1. Over $\mathcal G$ (symmetric, nonnegative, zero diagonal), the unique minimiser of $F$ is $\widehat G_{i,j}=e^{-\mathbf D_{i,j}/\tau}1_{\{i\ne j\}}$.
--   2. Over the nonnegative, zero-diagonal, right-stochastic matrices, the unique minimiser of $F$ is
--
--   $$\widehat G_{i,j}=\frac{e^{-\mathbf D_{i,j}/\tau}}{\sum_{k\ne i}e^{-\mathbf D_{i,k}/\tau}}1_{\{i\ne j\}}.$$
--
--   3. If $d$ is the cosine distance $1-\operatorname{CosSim}$, this row-normalised estimate is the SimCLR similarity estimate of eq. (3).
--
--   **Formalization Note** The paper states part 2 over $\mathcal G_{\rm rsto}$, which also requires symmetry. Its proof drops the symmetry constraint and claims the optimum is symmetric anyway, which is false in general: for $N=3$, $\tau=1$ and distances $\mathbf D_{12}=\mathbf D_{13}=1$, $\mathbf D_{23}=1.5$, the row-normalised kernel has $\widehat G_{12}=0.5\ne0.622=\widehat G_{21}$. The statement is the one the proof establishes, with the symmetry constraint removed. The paper's "$d$ any preferred metric" includes the cosine distance, which is not a metric, so only symmetry of $d$ is assumed. The identification with the Lifted Structured Loss is informal and is not included.
-- source:
--   Balestriero and LeCun, Contrastive and Non-Contrastive Self-Supervised Learning Recover Global and Local Spectral Embedding Methods, arXiv:2205.11508v3 (NeurIPS 2022), Section 4.1, Theorem 4, eqs. (14)-(16) and (3), p. 11 and p. 4; proof in Appendix A.10, pp. 27-28

import Mathlib
import Definitions.Def_SSLSpectralEmbedding_Basic

open Matrix

namespace SSLSpectralEmbedding

theorem graph_estimate_recovers_simclr {N K : ℕ} (hN : 2 ≤ N) (τ : ℝ) (hτ : 0 < τ)
    (d : (Fin K → ℝ) → (Fin K → ℝ) → ℝ) (hd : ∀ u v, d u v = d v u)
    (Z : Matrix (Fin N) (Fin K) ℝ) :
    (expKernel τ (distMat d Z) ∈ graphSet N ∧
      ∀ W ∈ graphSet N, W ≠ expKernel τ (distMat d Z) →
        graphObjective (distMat d Z) (entropyReg τ) (expKernel τ (distMat d Z)) <
          graphObjective (distMat d Z) (entropyReg τ) W) ∧
    (softmaxKernel τ (distMat d Z) ∈ rowStochSet N ∧
      ∀ W ∈ rowStochSet N, W ≠ softmaxKernel τ (distMat d Z) →
        graphObjective (distMat d Z) (entropyReg τ) (softmaxKernel τ (distMat d Z)) <
          graphObjective (distMat d Z) (entropyReg τ) W) ∧
    softmaxKernel τ (distMat cosineDist Z) = simclrSim τ Z := by sorry

end SSLSpectralEmbedding
