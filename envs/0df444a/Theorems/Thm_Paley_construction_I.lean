-- Prove2me | Theorems.Thm_Paley_construction_I
-- name    : Paley_construction_I
-- status  : Proved
-- author  : @ronr
-- created : 2026-09-05T21:38:02.221514+00:00
-- url     : https://prove2.me/theorems/65d083bb-43e4-4dfd-a728-69945984f8e0
-- title:
--   Paley's construction of Hadamard matrices from finite fields
-- statement:
--   This is Paley's 1933 construction of Hadamard matrices from finite fields (the case usually called Paley Construction I).
--
--   Let $F$ be a finite field of odd characteristic whose cardinality $q = |F|$ satisfies $q \equiv 3 \pmod 4$. Then there exists a $(q+1)\times(q+1)$ real matrix $M$ with every entry equal to $1$ or $-1$, satisfying the Hadamard orthogonality identity
--
--   $$
--   M M^{\mathsf T} = (q+1) \, I_{q+1}.
--   $$
--
--   **Construction.** Let $\chi$ denote the quadratic residue character of $F$ ($\chi(0)=0$, $\chi(a) = 1$ if $a$ is a nonzero square, $\chi(a) = -1$ otherwise). Form the bordered Jacobsthal matrix $C$, indexed by $\{\infty\} \cup F$, with $C_{\infty,\infty} = 0$, $C_{\infty,x} = 1$, $C_{x,\infty} = -1$, and $C_{x,y} = \chi(y - x)$ for $x, y \in F$. Since $q \equiv 3 \pmod 4$ forces $\chi(-1) = -1$, the matrix $C$ is skew-symmetric, and a direct character-sum computation shows $CC^{\mathsf T} = qI_{q+1}$. The matrix $M = C + I_{q+1}$ then has every entry $\pm1$ and satisfies $MM^{\mathsf T} = (q+1)I_{q+1}$.
--
--   Combined with Sylvester's doubling construction (Hadamard matrices of order $2^n$) and the Kronecker-product multiplicativity theorem for Hadamard matrices, this produces Hadamard matrices of many orders not reachable by Sylvester's construction alone — for instance $q = 11, 19, 23, 43$ give orders $12, 20, 24, 44$.
--
--   **Formalization Note** The statement is given in orthogonality form ($MM^{\mathsf T} = NI_N$) rather than the determinant form used elsewhere on the platform; the two are interderivable (see `hadamard_det_of_orthogonal` used in the `Hadamard_Conjecture` proof-sketch). The hypothesis `ringChar F ≠ 2` (odd characteristic) is listed explicitly alongside `Fintype.card F % 4 = 3`, even though the latter already implies the former as integers, to keep the statement's Lean hypotheses immediately usable without a separate derivation.
-- source:
--   R. E. A. C. Paley, On orthogonal matrices, Journal of Mathematics and Physics 12 (1933), 311-320 (the q ≡ 3 (mod 4) construction, sometimes called Paley Construction I). Formalized via the classical skew-conference-matrix route: bordered Jacobsthal matrix C with CC^T = qI (using the quadratic character's sum-to-zero property and the character-sum identity sum_z chi(z-x)chi(z-y) = -1 for x != y, both derived here from Mathlib's quadraticChar API), then M = C + I. See e.g. K. J. Horadam, Hadamard Matrices and Their Applications, Princeton University Press, 2007, Section 1.3, or J. H. van Lint and R. M. Wilson, A Course in Combinatorics, 2nd ed., Cambridge University Press, 2001, Chapter 18, for this standard presentation.

import Mathlib
open Matrix

theorem Paley_construction_I {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hchar : ringChar F ≠ 2) (hmod : Fintype.card F % 4 = 3) :
    ∃ M : Matrix (Fin (Fintype.card F + 1)) (Fin (Fintype.card F + 1)) ℝ,
      (∀ i j, M i j = 1 ∨ M i j = -1) ∧
        M * Mᵀ = ((Fintype.card F + 1 : ℕ) : ℝ) •
          (1 : Matrix (Fin (Fintype.card F + 1)) (Fin (Fintype.card F + 1)) ℝ) := by sorry
