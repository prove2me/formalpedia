-- Prove2me | Theorems.Thm_Transcendence_singular_matrix_subspace_annihilating_pair
-- name    : Transcendence.singular_matrix_subspace_annihilating_pair
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-01T12:33:21.97514+00:00
-- url     : https://prove2.me/theorems/23adddfc-7432-4ee3-a973-df9f43e8feb0
-- title:
--   Roy's lemma: a linear space of singular square matrices over an infinite field has a common annihilating pair
-- statement:
--   Let $F$ be an infinite field and $E$ a linear space of $n \times n$ matrices over $F$, all of them singular. Then there are non-zero $v, w \in F^n$ with
--
--   $$w^{\mathsf T} A\, v = 0 \quad\text{for every } A \in E.$$
--
--   This is the step that makes the Structural Rank Conjecture imply the Matrix Coefficient Conjecture of Dasgupta and Kakde.
--
--   **Proof.** Take $A_0 \in E$ of maximal rank $r < n$. For every $B \in E$, $B(\ker A_0) \subseteq \operatorname{Im} A_0$: otherwise, for all but finitely many $a$, the matrix $A_0 + aB \in E$ would have rank $r + 1$, because a determinant that is a polynomial in $a$ is non-zero at $a = 0$. Take $v \in \ker A_0$ and $w$ orthogonal to $\operatorname{Im} A_0$, both non-zero.
--
--   **Novelty.** None: this is Theorem 2.2 of Dasgupta–Kakde, *Ranks of matrices of logarithms of algebraic numbers II* (2024), whose printed proof they credit to D. Roy. A stronger form, $B(\ker A_0) \subseteq \operatorname{Im} A_0$ for $A_0$ of maximal rank, is Proposition 12.5 of Waldschmidt's *Diophantine Approximation on Linear Algebraic Groups* (2000), credited there to Roy (1990). The contribution of this node is the formal proof.
-- source:
--   S. Dasgupta and M. Kakde, Ranks of matrices of logarithms of algebraic numbers II: the Matrix Coefficient Conjecture, arXiv:2408.08178 (2024), Theorem 2.2 (p. 3), proof communicated by D. Roy; M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, Proposition 12.5 (p. 423), credited to Roy (1990, Prop. 3). Formal proof: Diaz modulus mission, 1 October 2026 (C. Perassi).

import Mathlib

open Matrix

namespace Transcendence

/-- **Roy's lemma** (Dasgupta–Kakde, *Ranks of matrices of logarithms of algebraic numbers II*, Theorem 2.2,
with Roy's proof). Over an infinite field, a linear space of singular `n × n` matrices has a common
annihilating pair: non-zero `v`, `w` with `wᵀ A v = 0` for every `A` in the space. -/
theorem singular_matrix_subspace_annihilating_pair {F : Type*} [Field F] [Infinite F] {n : ℕ}
    (E : Submodule F (Matrix (Fin n) (Fin n) F)) (hE : ∀ A ∈ E, A.det = 0) :
    ∃ v w : Fin n → F, v ≠ 0 ∧ w ≠ 0 ∧ ∀ A ∈ E, w ⬝ᵥ (A *ᵥ v) = 0 := by
  sorry

end Transcendence
