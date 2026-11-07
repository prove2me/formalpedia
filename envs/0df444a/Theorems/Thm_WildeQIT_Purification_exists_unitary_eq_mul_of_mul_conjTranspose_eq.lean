-- Prove2me | Theorems.Thm_WildeQIT_Purification_exists_unitary_eq_mul_of_mul_conjTranspose_eq
-- name    : WildeQIT.Purification.exists_unitary_eq_mul_of_mul_conjTranspose_eq
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T19:24:15.616032+00:00
-- url     : https://prove2.me/theorems/77f13d5c-d958-4304-a6ed-b5ab939376c9
-- title:
--   Unitary freedom: A A† = B B† implies A = B U with U unitary
-- statement:
--   Let $A,B$ be complex $m\times n$ matrices (rows indexed by a finite type $a$, columns by a finite type $n$) with $AA^\dagger=BB^\dagger$. Then there is a unitary $n\times n$ matrix $U$ with $A=BU$. Equivalently, if two families of $n$ vectors $a_x,b_x$ give the same operator $\sum_x|a_x\rangle\langle a_x|=\sum_x|b_x\rangle\langle b_x|$, then $a_x=\sum_j U_{jx}\,b_j$ for a unitary $U$. (Apply the previous lemma to $f=A^\dagger,\ g=B^\dagger$: $\|A^\dagger v\|^2=\langle v,AA^\dagger v\rangle=\|B^\dagger v\|^2$, so $A^\dagger=TB^\dagger$ for an isometry $T$, which is unitary in finite dimension; take $U=T^\dagger$.)
-- source:
--   Nielsen and Chuang, Quantum Computation and Quantum Information, Theorem 2.6 (unitary freedom in the ensemble for density matrices); Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, proof of Theorem 5.1.1 and Corollary 5.1.1, pp. 185-186

import Mathlib

namespace WildeQIT.Purification

open Matrix

/-- **Unitary freedom in `A Aᴴ = B Bᴴ`.** If two complex matrices `A B : Matrix a n ℂ` with
the same (finite) column index set satisfy `A * Aᴴ = B * Bᴴ`, then there is a unitary
`U ∈ Matrix.unitaryGroup n ℂ` with `A = B * U`. Equivalently, two families of `n` vectors
(the columns) whose outer-product sums `Σ_j |a_j⟩⟨a_j| = Σ_j |b_j⟩⟨b_j|` agree are related by a
unitary mixing: `a_x = Σ_j U_{j x} b_j` (Nielsen–Chuang Thm. 2.6). -/
theorem exists_unitary_eq_mul_of_mul_conjTranspose_eq {a n : Type*} [Fintype a] [Fintype n] [DecidableEq n]
    (A B : Matrix a n ℂ) (h : A * Aᴴ = B * Bᴴ) :
    ∃ U ∈ Matrix.unitaryGroup n ℂ, A = B * U := by sorry

end WildeQIT.Purification
