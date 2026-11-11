-- Prove2me | Theorems.Thm_PermInvCC_theorem_B_3
-- name    : PermInvCC.theorem_B_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:25:53.543199+00:00
-- url     : https://prove2.me/theorems/b66c1f96-fedc-4f37-91ea-4ad286935637
-- title:
--   Theorem B.3 — acceptance-matrix factorization $A=UV$, $\|U\|_F\le2^c\sqrt{|Y|}$, $\|V\|_F\le2^c\sqrt{|X|}$
-- statement:
--   Let $X,Y$ be finite input sets. The acceptance matrix $A(y,x)$ of a protocol using at most $c$ qubits with arbitrary prior entanglement admits a real factorization $A=UV$ with
--   $$\|U\|_F\le2^c\sqrt{|Y|},\qquad\|V\|_F\le2^c\sqrt{|X|},$$
--   where $\|\cdot\|_F$ is the Frobenius norm.
--
--   This is the $\gamma_2$ method of Linial and Shraibman in the Frobenius form of Sherstov–Storozhenko; it turns a cheap protocol into a low-norm bilinear form.
--
--   Differences from the source:
--   - encoding: c-qubit protocol with arbitrary prior entanglement → EntQProtocol X Y of cost ≤ c; reason: the model of Definition 2.1 as formalized in EntQProtocol
--   - reading: arbitrary prior entanglement → an arbitrary input-independent unit start state on finitely many qubits W (W unbounded); reason: the standard finite-dimensional model of entanglement-assisted communication, the one of [LS09] and [SS24, Thm 2.22] on which the paper builds its quantum bounds (App. B.3); the paper never uses an infinite-dimensional state
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Theorem B.3, p.43

import Mathlib
import Definitions.Def_PermInvCC_EntQProtocol
import Definitions.Def_PermInvCC_acceptMatrix

namespace PermInvCC

/-- **Theorem B.3 (Quantum Acceptance-Matrix Factorization (γ₂ Method), [SS24, Theorem 2.22,
full version])** (Y. Huang and Z. Ye, arXiv:2609.40116, held version sha256 fe1797dd…, p.43). Let
`X, Y` be finite input sets. The acceptance matrix `A(y, x)` of a `c`-qubit protocol with
arbitrary prior entanglement admits a real factorization `A = UV` satisfying
`‖U‖_F ≤ 2^c √|Y|` and `‖V‖_F ≤ 2^c √|X|`, where `‖·‖_F` is the Frobenius norm.

**Formalization Note.** A `c`-qubit protocol is an `EntQProtocol` of cost at most `c`; the inner
dimension `k` of the factorization is any natural number; the Frobenius norm is written out as
the square root of the sum of squared entries. -/
theorem theorem_B_3 (X Y : Type) [Fintype X] [Fintype Y] (P : EntQProtocol X Y) (c : ℕ)
    (hc : P.cost ≤ c) :
    ∃ (k : ℕ) (U : Matrix Y (Fin k) ℝ) (V : Matrix (Fin k) X ℝ), acceptMatrix P = U * V ∧
      Real.sqrt (∑ i, ∑ j, U i j ^ 2) ≤ 2 ^ c * Real.sqrt (Fintype.card Y) ∧
      Real.sqrt (∑ i, ∑ j, V i j ^ 2) ≤ 2 ^ c * Real.sqrt (Fintype.card X) := by sorry

end PermInvCC
