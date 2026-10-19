-- Prove2me | Theorems.Thm_Paley_construction_II
-- name    : Paley_construction_II
-- status  : Proved
-- author  : @ronr
-- created : 2026-09-05T23:12:57.161552+00:00
-- url     : https://prove2.me/theorems/087846e2-e39f-4fe7-abfc-c09366c76aa9
-- title:
--   Paley's second construction of Hadamard matrices from finite fields
-- statement:
--   This is Paley's second (1933) construction of Hadamard matrices from finite fields, complementary to `Paley_construction_I`.
--
--   Let $F$ be a finite field of odd characteristic whose cardinality $q = |F|$ satisfies $q \equiv 1 \pmod 4$. Then there exists a $2(q+1)\times2(q+1)$ real matrix $M$ with every entry equal to $1$ or $-1$, satisfying the Hadamard orthogonality identity
--
--   $$
--   M M^{\mathsf T} = 2(q+1) \, I_{2(q+1)}.
--   $$
--
--   **Construction.** As in `Paley_construction_I`, let $\chi$ be the quadratic residue character of $F$ and form the bordered Jacobsthal matrix $C$ indexed by $\{\infty\}\cup F$, but now with a *symmetric* border ($C_{\infty,x}=C_{x,\infty}=1$, matching the fact that $q\equiv1\pmod4$ gives $\chi(-1)=1$, making $C$ itself symmetric: $C^{\mathsf T}=C$). The same character-sum computation as in Paley I gives $CC^{\mathsf T}=qI_{q+1}$, i.e. (using symmetry) $C^2=qI_{q+1}$.
--
--   Set $A=C+I$ and $B=C-I$ (each with entries $\pm1$, both symmetric). Since $AB=BA=C^2-I=(q-1)I$ is already scalar, $A$ and $B$ commute, and $A^2+B^2=2C^2+2I=2(q+1)I$. The block matrix
--
--   $$
--   M=\begin{pmatrix}A&B\\B&-A\end{pmatrix}
--   $$
--
--   is then symmetric with $M^2 = \begin{pmatrix}A^2+B^2&AB-BA\\BA-AB&B^2+A^2\end{pmatrix} = 2(q+1)I_{2(q+1)}$, giving the required Hadamard matrix of order $2(q+1)$.
--
--   Combined with `Paley_construction_I`, `Hadamard_matrix_kronecker_product`, and Sylvester's doubling construction, this gives Hadamard matrices for further orders not reachable by the earlier constructions alone — for instance $q=5,13,17,29$ give orders $12,28,36,60$.
--
--   **Formalization Note** The statement is given in orthogonality form, matching `Paley_construction_I`. The two source matrices $A,B$ of order $q+1$ are combined into the order-$2(q+1)$ result via `Matrix.fromBlocks`, transported at the end from the natural index type `Option F ⊕ Option F` to `Fin (2*(Fintype.card F + 1))`.
-- source:
--   R. E. A. C. Paley, On orthogonal matrices, Journal of Mathematics and Physics 12 (1933), 311-320 (the q ≡ 1 (mod 4) construction, sometimes called Paley Construction II). Formalized via the same bordered Jacobsthal/conference-matrix route as Paley_construction_I (65d083bb-43e4-4dfd-a728-69945984f8e0), now with symmetric border, combined into the order-2(q+1) result via the classical 2x2 block construction M = [[A,B],[B,-A]] with A=C+I, B=C-I. See e.g. K. J. Horadam, Hadamard Matrices and Their Applications, Princeton University Press, 2007, Section 1.3, or J. H. van Lint and R. M. Wilson, A Course in Combinatorics, 2nd ed., Cambridge University Press, 2001, Chapter 18.

import Mathlib
open Matrix

theorem Paley_construction_II {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hchar : ringChar F ≠ 2) (hmod : Fintype.card F % 4 = 1) :
    ∃ M : Matrix (Fin (2 * (Fintype.card F + 1))) (Fin (2 * (Fintype.card F + 1))) ℝ,
      (∀ i j, M i j = 1 ∨ M i j = -1) ∧
        M * Mᵀ = ((2 * (Fintype.card F + 1) : ℕ) : ℝ) •
          (1 : Matrix (Fin (2 * (Fintype.card F + 1))) (Fin (2 * (Fintype.card F + 1))) ℝ) := by sorry
