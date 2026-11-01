-- Prove2me | Theorems.Thm_WildeQIT_Purification_polar_decomposition
-- name    : WildeQIT.Purification.polar_decomposition
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:19:41.654414+00:00
-- url     : https://prove2.me/theorems/e395bc85-eaec-4701-95ce-93574a5ed661
-- title:
--   Polar decomposition $A = U\sqrt{A^\dagger A} = \sqrt{AA^\dagger}\,V$ (Theorem A.0.1)
-- statement:
--   Let $A$ be an operator on a finite-dimensional Hilbert space $\mathcal H$. Then $A$ admits a **left polar decomposition** and a **right polar decomposition**: there are unitary operators $U$ and $V$ on $\mathcal H$ with
--
--   $$
--   A = U\sqrt{A^\dagger A}\qquad\text{and}\qquad A = \sqrt{AA^\dagger}\,V,
--   $$
--
--   where $\sqrt{\cdot}$ is the positive semidefinite square root of a positive semidefinite operator.
--
--   The polar decomposition writes an arbitrary operator as a unitary times its absolute value $|A| = \sqrt{A^\dagger A}$; the book uses it, for instance, in the equality condition of Hölder's inequality (p. 367) and in fidelity arguments.
--
--   **Formalization Note** Operators are square complex matrices indexed by a finite type, unitarity is membership in `Matrix.unitaryGroup`, and $\sqrt{\cdot}$ is Mathlib's `CFC.sqrt`.
--
--   Differences from the source:
--   - reading: "$U$" and "$V$", unqualified → unitary $U$ and $V$; reason: the proof on p. 740 takes $V = U_1U_2$, a product of the two unitaries of a singular value decomposition, and p. 367 cites Theorem A.0.1 for "a unitary such that $B = U|B|$"; this is the standard meaning of a polar decomposition (and the stronger reading).
--   - reading: "any operator $A$" → any $A\in\mathcal L(\mathcal H)$ (a square matrix); reason: the book writes $\mathcal L(\mathcal H)$ for square operators and $\mathcal L(\mathcal H,\mathcal H')$ when it means rectangular ones, the proof's product $U_1U_2$ requires both unitaries to act on one space, and a unitary $U$ with $A = U\sqrt{A^\dagger A}$ exists only for square $A$.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem A.0.1, p. 740

import Mathlib

open scoped Matrix MatrixOrder

namespace WildeQIT.Purification

/-- **Theorem A.0.1 (Polar Decomposition).** Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, Theorem A.0.1, p. 740: "Any operator A admits a left polar decomposition
A = U√(A†A), and a right polar decomposition A = √(AA†)V."

For every operator `A : Matrix n n ℂ` on a finite-dimensional Hilbert space there are unitaries
`U` and `V` with `A = U · √(Aᴴ A)` and `A = √(A Aᴴ) · V`, where `√` is the positive
semidefinite square root (`CFC.sqrt`).

**Formalization Note.** `U` and `V` are unitary (`Matrix.unitaryGroup`): the statement leaves
them unqualified, and the proof on p. 740 takes `V = U₁U₂`, a product of the two unitaries of a
singular value decomposition. Operators act on one finite-dimensional space (square matrices),
as the proof's product `U₁U₂` requires. -/
theorem polar_decomposition {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    (∃ U ∈ Matrix.unitaryGroup n ℂ, A = U * CFC.sqrt (Aᴴ * A)) ∧
      (∃ V ∈ Matrix.unitaryGroup n ℂ, A = CFC.sqrt (A * Aᴴ) * V) := by sorry

end WildeQIT.Purification
