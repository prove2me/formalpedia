-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P09_qubit_explicit_completion
-- name    : QAlgorithms.Papers.Independent.Support21.P09.qubit_explicit_completion
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:46:56.908476+00:00
-- url     : https://prove2.me/theorems/16bab6cf-f24c-48ae-b857-2ee70a0025d1
-- title:
--   Explicit complex qubit unitary completion
-- statement:
--   For $a,b\in\mathbb C$ with $|a|^2+|b|^2=1/2$, define
--
--   $$
--   B=\begin{pmatrix}
--   a&a&b&b\ b&-b&a&-a\ \overline b&\overline b&-\overline a&-\overline a\ -\overline a&\overline a&\overline b&-\overline b
--   \end{pmatrix}.
--   $$
--
--   Then $B\in U(4)$ and its first two rows equal the defining matrix $M$ of Example 4. For the Pauli matrices $X,Z$ and the monomial generators $R_X,R_Z$ described there,
--
--   $$
--   (Z\oplus Z)B=BR_Z,\qquad (X\oplus X)B=BR_X.
--   $$
--
--   These are the symmetries on the generators of the ordinary Pauli lift. For every qubit density matrix $\rho$ and each of the four labels,
--
--   $$
--   [B^\dagger(\rho\oplus0_2)B]_{jj}=\operatorname{tr}(\rho M_{:,j}M_{:,j}^\dagger).
--   $$
--
--   Thus the adjoint of this completion implements the indexed qubit POVM, including parameters giving repeated effects.
-- source:
--   Implementation of group-covariant POVMs by orthogonal measurements, arXiv:quant-ph/0407054v1, PDF p. 12, Example 7: explicit qubit unitary completion

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P09

open scoped BigOperators ComplexConjugate

open QAlgorithms.Papers.Independent.Frontier18.P17 (clock)

/-- PDF pp.11–12, Example 7: explicit complex unitary completion and its Pauli-lift
symmetry (on the two generating elements), with exact probabilities for all input states. -/
theorem qubit_explicit_completion (a b : ℂ) (hnorm : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1 / 2) :
    qubitCompletion a b ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
    (∀ i j, qubitCompletion a b (Fin.castAdd 2 i) j = qubitColumns a b i j) ∧
    sumBlock pauliZFin pauliZFin * qubitCompletion a b = qubitCompletion a b * pauliRZ ∧
    sumBlock pauliXFin pauliXFin * qubitCompletion a b = qubitCompletion a b * pauliRX ∧
    ImplementsPOVM (qubitColumns a b) (qubitCompletion a b).conjTranspose
      (Fin.castAdd 2) := by sorry

end QAlgorithms.Papers.Independent.Support21.P09

end
