-- Prove2me | Theorems.Thm_WhitneyMatroid_Binary_exists_unique_binary_representation
-- name    : WhitneyMatroid.Binary.exists_unique_binary_representation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T05:04:23.86415+00:00
-- url     : https://prove2.me/theorems/c18e5c4d-a17f-4a4d-bf75-4fca915482f0
-- title:
--   Theorem 37 — every (C*)-matroid is the matroid of a matrix mod 2, uniquely given the base columns
-- statement:
--   Let $M$ be any matroid satisfying Postulate (C\*). Suppose $\rho(M) = n$, so $M$ consists of the elements $e_1, \dots, e_n$, and that $e_1 + \dots + e_{n-q}$ is a base of $M$. Let $\mathbf M_1$ be any matrix of integers (mod 2), with any number $m$ of rows, having $n - q$ columns $C_1, \dots, C_{n-q}$ which are independent (mod 2). Then columns $C_{n-q+1}, \dots, C_n$ can be adjoined in a unique manner to $\mathbf M_1$, forming a matrix
--
--   $$\mathbf M = \big(\, \mathbf M_1 \;\big|\; C_{n-q+1} \cdots C_n \,\big)$$
--
--   of which the corresponding matroid is $M$.
--
--   Together with the appendix result that the matroid of any matrix mod 2 satisfies (C\*), this characterizes the matroids corresponding to matrices of integers mod 2 (the binary matroids) as exactly those satisfying (C\*), and shows that a representation is fixed once the columns of one base are chosen.
--
--   **Formalization Note** Elements are `Fin (r + q)` with $e_k \mapsto k-1$ and $r = n - q$, so the base is the range of `Fin.castAdd q`; the ground set of `M` is all of `Fin (r + q)` (that is $\rho(M) = n$). The matrices are `Matrix (Fin m) (Fin r) (ZMod 2)` and `Matrix (Fin m) (Fin (r + q)) (ZMod 2)`; "adjoined to $\mathbf M_1$" means the first $r$ columns of $\mathbf M$ are those of $\mathbf M_1$, and "the corresponding matroid is $M$" is `IsMatroidOf M A` (same independent sets). Uniqueness is of the whole matrix $\mathbf M$ under these two conditions. Independence of the columns of $\mathbf M_1$ is linear independence over `ZMod 2` of its transpose's rows.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 533, Theorem 37

import Mathlib
import Definitions.Def_WhitneyMatroid_Binary_Cycles
import Definitions.Def_WhitneyMatroid_Binary_IsMatroidOf

namespace WhitneyMatroid.Binary

/-- Theorem 37 (Appendix, p. 533). Let `M` be any matroid satisfying (C*). Suppose `ρ(M) = n`
(the elements are `e₁, …, eₙ`, here `Fin (r + q)` with `e_k ↦ k - 1`, all of them in `M`), and
`e₁ + ⋯ + e_{n-q}` is a base. Then if `A₁` is any matrix of integers (mod 2) with `n - q = r`
columns which are independent (mod 2), columns `C_{n-q+1}, …, Cₙ` can be adjoined in a unique
manner to `A₁`, forming a matrix `A` of which the corresponding matroid is `M`. -/
theorem exists_unique_binary_representation {r q m : ℕ} (M : Matroid (Fin (r + q)))
    (hE : M.E = Set.univ) (hC : SatisfiesCStar {C | M.IsCircuit C})
    (hB : M.IsBase (Set.range (Fin.castAdd q : Fin r → Fin (r + q))))
    (A₁ : Matrix (Fin m) (Fin r) (ZMod 2))
    (hA₁ : LinearIndependent (ZMod 2) A₁.transpose) :
    ∃! A : Matrix (Fin m) (Fin (r + q)) (ZMod 2),
      (∀ i : Fin m, ∀ j : Fin r, A i (Fin.castAdd q j) = A₁ i j) ∧ IsMatroidOf M A := by sorry

end WhitneyMatroid.Binary
