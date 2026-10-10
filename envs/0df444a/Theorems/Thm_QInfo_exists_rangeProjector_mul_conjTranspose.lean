-- Prove2me | Theorems.Thm_QInfo_exists_rangeProjector_mul_conjTranspose
-- name    : QInfo.exists_rangeProjector_mul_conjTranspose
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-09T14:44:17.300846+00:00
-- url     : https://prove2.me/theorems/774c34d9-657b-464d-afdb-d356a0079c94
-- title:
--   Pseudo-inverse of the Gram matrix $WW^\dagger$ fixes the range of $W$
-- statement:
--   Let $W$ be a complex $m\times n$ matrix (finite index types) and let $G = WW^\dagger$, a positive semidefinite Hermitian $m\times m$ matrix. Then there is a Hermitian matrix $G^+$ that commutes with $G$ and satisfies
--   $$G\,G^+\,W = W .$$
--   In words: $GG^+$ acts as the identity on the range of $W$ (which equals the range, i.e. the support, of $G$). (For instance the Moore–Penrose pseudo-inverse of $G$ has these properties; then $GG^+$ is the orthogonal projector onto $\operatorname{ran} G = \operatorname{ran} W$.)
--
--   This is the standard device behind "restrict to the support of the density matrix" arguments in quantum information, e.g. restricting $\bar E$ to the support of $\rho_{\bar E}$ in Appendix B of Almheiri–Dong–Harlow.
--
--   **Formalization Note.** $W^\dagger$ is `Wᴴ` (`Matrix.conjTranspose`). The statement only asks for existence of $G^+$ with the three properties used downstream (Hermitian, commuting with $G$, $GG^+W = W$).
-- source:
--   Standard linear algebra (Moore–Penrose pseudo-inverse via the spectral theorem); used for Almheiri, Dong, Harlow, Bulk Locality and Quantum Error Correction in AdS/CFT, JHEP 04 (2015) 163, https://arxiv.org/abs/1411.7041, Appendix B, around Eq. (B.15).

import Mathlib
open Matrix

namespace QInfo
theorem exists_rangeProjector_mul_conjTranspose {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] (W : Matrix m n ℂ) :
    ∃ Gp : Matrix m m ℂ, Gp.IsHermitian ∧ (W * Wᴴ) * Gp = Gp * (W * Wᴴ) ∧
      (W * Wᴴ) * Gp * W = W := by sorry
end QInfo
