-- Prove2me | Theorems.Thm_PropVolSampling_Reduction_identity_6
-- name    : PropVolSampling.Reduction.identity_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:48:29.855909+00:00
-- url     : https://prove2.me/theorems/dd9235b2-bd4a-44f6-869f-66d85d6b584a
-- title:
--   Identity (6), p. 8 — $\operatorname{tr}M^{-1}=E_{d-1}(M)/\det M$
-- statement:
--   Let $d\ge 1$ and let $M$ be a real symmetric $d\times d$ matrix of rank $d$ ($\det M\ne 0$), with eigenvalues $\lambda_1,\dots,\lambda_d$. Then
--   $$\operatorname{tr}M^{-1}=\sum_{i=1}^d\frac1{\lambda_i(M)}=\frac{e_{d-1}(\lambda(M))}{e_d(\lambda(M))}=\frac{E_{d-1}(M)}{\det M}.$$
--
--   This observation of Avron and Boutsidis rewrites the A-objective as a ratio of two spectral elementary symmetric functions, to which identity (4) applies.
--
--   **Formalization Note** The page states (6) for a $d\times d$ matrix of rank $d$ in a context where $E_k$ is defined for positive semidefinite matrices. The Lean statement assumes $M$ symmetric with $\det M\ne0$ (so the eigenvalues are real and the characteristic polynomial splits), which includes the positive definite case; $1\le d$ is added because $d-1$ is natural-number subtraction.
-- source:
--   Nikolov, Singh, Tantipongpipat, Proportional Volume Sampling and Approximation Algorithms for A-Optimal Design, arXiv:1802.08318v5, p. 8, identity (6)

import Mathlib
import Definitions.Def_PropVolSampling_Reduction_Model

namespace PropVolSampling.Reduction
open Matrix Finset

theorem identity_6 {d : ℕ} (hd : 1 ≤ d) (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsHermitian)
    (hdet : M.det ≠ 0) :
    aObj M = Ek (d - 1) M / M.det := by sorry

end PropVolSampling.Reduction
