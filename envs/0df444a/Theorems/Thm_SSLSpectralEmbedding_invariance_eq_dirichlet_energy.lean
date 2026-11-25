-- Prove2me | Theorems.Thm_SSLSpectralEmbedding_invariance_eq_dirichlet_energy
-- name    : SSLSpectralEmbedding.invariance_eq_dirichlet_energy
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T06:24:02.974799+00:00
-- url     : https://prove2.me/theorems/1b9750f1-f3a4-43f4-8b08-703319d2b497
-- title:
--   Eq. (7): the VICReg invariance term is twice the Dirichlet energy
-- statement:
--   Let $G\in\mathbb{R}^{N\times N}$ be a relation matrix (symmetric, nonnegative entries, zero diagonal), let $D=\operatorname{diag}(G\mathbf 1)$ and $L=D-G$. For every $Z\in\mathbb{R}^{N\times K}$,
--
--   $$\sum_{i=1}^N\sum_{j=1}^N G_{i,j}\,\|Z_{i,.}-Z_{j,.}\|_2^2=2\operatorname{Tr}\big(Z^\top LZ\big).$$
--
--   The VICReg invariance term is thus twice the Dirichlet energy of the signal $Z$ on the graph $G$. The proofs of Theorems 1 and 2 use this identity.
-- source:
--   Balestriero and LeCun, Contrastive and Non-Contrastive Self-Supervised Learning Recover Global and Local Spectral Embedding Methods, arXiv:2205.11508v3 (NeurIPS 2022), Section 3.1, eq. (7), p. 6; proof in Appendix A.5, p. 24

import Mathlib
import Definitions.Def_SSLSpectralEmbedding_Basic

open Matrix

namespace SSLSpectralEmbedding

theorem invariance_eq_dirichlet_energy {N K : ℕ} (G : Matrix (Fin N) (Fin N) ℝ)
    (hG : IsRelationMatrix G) (Z : Matrix (Fin N) (Fin K) ℝ) :
    pairSum G Z = 2 * (Zᵀ * laplacian G * Z).trace := by sorry

end SSLSpectralEmbedding
