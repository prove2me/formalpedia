-- Prove2me | Theorems.Thm_QInfo_commute_mul_conjTranspose_iff_exists_mirror
-- name    : QInfo.commute_mul_conjTranspose_iff_exists_mirror
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-09T14:44:18.583168+00:00
-- url     : https://prove2.me/theorems/82129820-4f57-4e0a-8f7c-e4580b38c49f
-- title:
--   Mirror lemma: $[A, WW^\dagger]=0$ iff $A$ is mirrored through $W$
-- statement:
--   Let $W$ be a complex $m\times n$ matrix and $A$ a complex $m\times m$ matrix (finite index types). Then $A$ commutes with $WW^\dagger$ if and only if there is an $n\times n$ matrix $B$ with
--   $$A\,W = W\,B \qquad\text{and}\qquad A^\dagger\,W = W\,B^\dagger .$$
--
--   Physically: view $W$ as a pure state $|\psi\rangle \in \mathcal H_m\otimes\mathcal H_n$ with reduced density matrix $\rho_m = WW^\dagger$. An operator $A$ on the first factor commutes with $\rho_m$ iff it has a "mirror" operator $B$ on the second factor acting the same way on $|\psi\rangle$, together with its adjoint. This is the key step (B.14)$\Rightarrow$(B.15)–(B.17) in Appendix B of Almheiri–Dong–Harlow, where the operator $O_R\otimes 1_E$ commuting with $\rho_{RE}$ is transferred to an operator on $\bar E$.
--
--   **Formalization Note.** $W^\dagger$ is `Wᴴ`.
-- source:
--   Almheiri, Dong, Harlow, Bulk Locality and Quantum Error Correction in AdS/CFT, JHEP 04 (2015) 163, https://arxiv.org/abs/1411.7041, Appendix B, Eqs. (B.14)–(B.17)

import Mathlib
open Matrix

namespace QInfo
theorem commute_mul_conjTranspose_iff_exists_mirror {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] (W : Matrix m n ℂ) (A : Matrix m m ℂ) :
    A * (W * Wᴴ) = (W * Wᴴ) * A ↔ ∃ B : Matrix n n ℂ, A * W = W * B ∧ Aᴴ * W = W * Bᴴ := by sorry
end QInfo
