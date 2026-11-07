-- Prove2me | Theorems.Thm_WildeQIT_Purification_exists_coisometry_eq_mul_of_mul_conjTranspose_eq
-- name    : WildeQIT.Purification.exists_coisometry_eq_mul_of_mul_conjTranspose_eq
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T19:42:21.339598+00:00
-- url     : https://prove2.me/theorems/c70bc5e2-98ad-4521-b40e-13eb2c4443fd
-- title:
--   Rectangular unitary freedom: $AA^\dagger = BB^\dagger$ implies $A = BV$ with $VV^\dagger = I$
-- statement:
--   Let $A$ be a complex $k\times m$ matrix and $B$ a complex $k\times n$ matrix (rows indexed by one finite set, columns by finite sets of sizes $m$ and $n$) with $n\le m$. If
--
--   $$AA^\dagger = BB^\dagger,$$
--
--   then there is an $n\times m$ matrix $V$ with orthonormal rows, $VV^\dagger = I_n$, such that $A = BV$. In ensemble language: if two families of vectors $\{a_x\}_{x=1}^{m}$ and $\{b_y\}_{y=1}^{n}$ with $n\le m$ give the same operator $\sum_x |a_x\rangle\langle a_x| = \sum_y |b_y\rangle\langle b_y|$, then $a_x = \sum_y V_{y x}\, b_y$. This is the rectangular form of the unitary freedom in ensembles and purifications; it gives the isometry relating two purifications with reference systems of different dimensions.
--
--   **Formalization Note.** `V * Vᴴ = 1` is stated for `V : Matrix n m ℂ`; equivalently $V^\dagger$ is an isometry ($\mathbb C^n\to\mathbb C^m$).
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, proof of Theorem 5.1.1, p. 185; Nielsen and Chuang, Quantum Computation and Quantum Information, Theorem 2.6

import Mathlib

namespace WildeQIT.Purification

open Matrix

/-- **Rectangular unitary freedom.** Let `A : Matrix a m ℂ` and `B : Matrix a n ℂ` be complex
matrices with the same (finite) row index set and `card n ≤ card m`. If `A * Aᴴ = B * Bᴴ`, then
there is a co-isometry `V : Matrix n m ℂ` (`V * Vᴴ = 1`, i.e. orthonormal rows) with
`A = B * V`. Equivalently, if `∑_{x ∈ m} |a_x⟩⟨a_x| = ∑_{y ∈ n} |b_y⟩⟨b_y|` with at most as
many vectors `b_y` as `a_x`, then `a_x = ∑_y V_{y x} b_y` for such a `V`. -/
theorem exists_coisometry_eq_mul_of_mul_conjTranspose_eq {a m n : Type*} [Fintype a] [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (A : Matrix a m ℂ) (B : Matrix a n ℂ) (hcard : Fintype.card n ≤ Fintype.card m)
    (h : A * Aᴴ = B * Bᴴ) :
    ∃ V : Matrix n m ℂ, V * Vᴴ = 1 ∧ A = B * V := by sorry

end WildeQIT.Purification
