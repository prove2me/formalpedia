-- Prove2me | Theorems.Thm_SSLSpectralEmbedding_vicreg_constrained_recovers_laplacian_eigenmaps
-- name    : SSLSpectralEmbedding.vicreg_constrained_recovers_laplacian_eigenmaps
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:24:56.224498+00:00
-- url     : https://prove2.me/theorems/cb4c9f9d-a4fc-462a-8ec4-fda5530c81aa
-- title:
--   Theorem 2 (as proved): constrained VICReg is solved by rescaled Laplacian Eigenmaps
-- statement:
--   Let $G$ be a relation matrix on $N$ samples whose degree matrix is isotropic, $D=cI$ with $c>0$, as for the graph of $V$ views of each sample ($c=V-1$). Let $1\le K\le N-1$ and $\alpha,\beta>0$, $\gamma\ge0$. A Laplacian-Eigenmaps solution $Z^*_{\rm LE}$ is a minimiser of $\operatorname{Tr}(Z^\top(D-G)Z)$ over $Z\in\mathbb{R}^{N\times K}$ with $Z^\top DZ=I$ and columns of zero mean. Then:
--
--   1. a Laplacian-Eigenmaps solution exists;
--   2. for every Laplacian-Eigenmaps solution $Z^*_{\rm LE}$, the rescaled matrix $\widetilde Z=\sqrt{cN}\,Z^*_{\rm LE}$ satisfies $\mathcal L_{\rm var}(\widetilde Z)=\mathcal L_{\rm cov}(\widetilde Z)=0$, and
--
--   $$\mathcal L_{\rm vic}(\widetilde Z)=\min_{Z\in\mathbb{R}^{N\times K}}\ \mathcal L_{\rm inv}(Z)\quad\text{s.t. }\mathcal L_{\rm var}(Z)=0\text{ and }\mathcal L_{\rm cov}(Z)=0,$$
--
--   where $\mathcal L_{\rm vic}=\alpha\mathcal L_{\rm var}+\beta\mathcal L_{\rm cov}+\mathcal L_{\rm inv}$ is the VICReg loss of eq. (2) with its hinge variance term.
--
--   So the constrained VICReg problem is solved by Laplacian Eigenmaps, and $\alpha,\beta$ play no role.
--
--   **Formalization Note** The printed theorem evaluates $\mathcal L_{\rm vic}$ at $Z^*_{\rm LE}$ itself. Because $Z^*_{\rm LE}$ is normalised by $Z^\top DZ=I$, its covariance is $\frac1{cN}I$, so it does not satisfy the constraint unless $cN=1$. The proof (Appendix A.8) works "up to a rescaling" with $Z^\top Z=\frac Nc I$. The statement uses that rescaling, and it assumes $D=cI$, which the proof uses. The minimum is written as "$\mathcal L_{\rm vic}(\widetilde Z)\le\mathcal L_{\rm inv}(Z)$ for every feasible $Z$" together with feasibility of $\widetilde Z$. The hypothesis $\gamma\ge0$ is necessary: for $\gamma<0$, scaling a feasible $Z$ up keeps it feasible and sends $\mathcal L_{\rm inv}$ to $-\infty$.
-- source:
--   Balestriero and LeCun, Contrastive and Non-Contrastive Self-Supervised Learning Recover Global and Local Spectral Embedding Methods, arXiv:2205.11508v3 (NeurIPS 2022), Section 3.2, Theorem 2, eq. (11), p. 9; proof in Appendix A.8, p. 26

import Mathlib
import Definitions.Def_SSLSpectralEmbedding_Basic

open Matrix

namespace SSLSpectralEmbedding

theorem vicreg_constrained_recovers_laplacian_eigenmaps {N K : ℕ} (hKN : K + 1 ≤ N)
    (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 ≤ γ)
    (G : Matrix (Fin N) (Fin N) ℝ) (hG : IsRelationMatrix G)
    (c : ℝ) (hc : 0 < c) (hdeg : ∀ i, ∑ j, G i j = c) :
    (∃ Z : Matrix (Fin N) (Fin K) ℝ, IsLESolution G Z) ∧
    ∀ ZLE : Matrix (Fin N) (Fin K) ℝ, IsLESolution G ZLE →
      varTerm (Real.sqrt (c * N) • ZLE) = 0 ∧ covTerm (Real.sqrt (c * N) • ZLE) = 0 ∧
      ∀ Z : Matrix (Fin N) (Fin K) ℝ, varTerm Z = 0 → covTerm Z = 0 →
        vicLoss α β γ G (Real.sqrt (c * N) • ZLE) ≤ invTerm γ G Z := by sorry

end SSLSpectralEmbedding
