-- Prove2me | Theorems.Thm_PropVolSampling_Reduction_identity_4
-- name    : PropVolSampling.Reduction.identity_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:48:26.949979+00:00
-- url     : https://prove2.me/theorems/53c881bc-f1dc-40a2-825f-2bb16297dc98
-- title:
--   Identity (4), p. 8 — $E_k(VV^\top)=E_k(V^\top V)=\sum_{S\in\mathcal U_k}\det(V_S^\top V_S)$
-- statement:
--   Let $V$ be a real $d\times n$ matrix and $k\ge 0$. With $E_k(M)$ the $k$-th elementary symmetric polynomial of the eigenvalues of $M$ and $\mathcal U_k$ the $k$-element subsets of $[n]$,
--   $$E_k(VV^\top)=E_k(V^\top V)=\sum_{S\in\mathcal U_k}\det(V_S^\top V_S).$$
--
--   This extends the Cauchy–Binet formula from the determinant ($k=d$) to all $E_k$; it is the identity that turns both the expected objective of proportional volume sampling and the relaxation's objective into sums over $(d-1)$- and $d$-subsets.
--
--   **Formalization Note** $E_k$ is `Multiset.esymm k` of the real roots of the characteristic polynomial; $VV^\top$ ($d\times d$) and $V^\top V$ ($n\times n$) are symmetric, so the characteristic polynomials split. The identity is stated for every $k$ (both sides vanish for $k>\min(d,n)$).
-- source:
--   Nikolov, Singh, Tantipongpipat, Proportional Volume Sampling and Approximation Algorithms for A-Optimal Design, arXiv:1802.08318v5, p. 8, identity (4)

import Mathlib
import Definitions.Def_PropVolSampling_Reduction_Model

namespace PropVolSampling.Reduction
open Matrix Finset

theorem identity_4 {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ) (k : ℕ) :
    Ek k (V * Vᵀ) = Ek k (Vᵀ * V) ∧
      Ek k (Vᵀ * V) = ∑ S ∈ powersetCard k (univ : Finset (Fin n)),
        ((colSub V S)ᵀ * colSub V S).det := by sorry

end PropVolSampling.Reduction
