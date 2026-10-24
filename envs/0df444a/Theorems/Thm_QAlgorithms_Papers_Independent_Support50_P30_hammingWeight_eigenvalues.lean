-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P30_hammingWeight_eigenvalues
-- name    : QAlgorithms.Papers.Independent.Support50.P30.hammingWeight_eigenvalues
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:26:46.415746+00:00
-- url     : https://prove2.me/theorems/bdd9b565-d8b8-4adc-967c-232bc27330b7
-- title:
--   Lemma 4 (Eigenvalues in terms of Hamming weights)
-- statement:
--   For a computational basis string $z\in\{0,1\}^n$, let $w(z)$ be its Hamming weight. The three unnormalized diagonal Pauli operators satisfy
--
--   $$\left(\sum_j Z_j\right)|z\rangle=(n-2w(z))|z\rangle,$$
--   $$\left(\sum_{k<j}Z_jZ_k\right)|z\rangle=\frac{n^2-n(4w(z)+1)+4w(z)^2}{2}|z\rangle,\qquad
--   \left(\prod_jZ_j\right)|z\rangle=(-1)^{w(z)}|z\rangle.$$
--
--   All subtraction is signed real or complex arithmetic. At $n=0$ the sums are zero and the product is the identity. These identities supply computational-basis eigenvalues used by the block calculations.
-- source:
--   Theoretical Guarantees for Permutation-Equivariant Quantum Neural Networks, arXiv:2210.09974v3, PDF p. 27, Lemma 4 (Eigenvalues in terms of Hamming weights)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P30

noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator NNReal ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P30

attribute [local instance] LieRing.ofAssociativeRing

/-- PDF p.27, Lemma 4: all three eigenvector identities, also at n=0. -/
theorem hammingWeight_eigenvalues (n : ℕ) (z : Qubits n) :
    act (collective n pauliZ 1) (ket z) =
      (((n : ℂ) - 2 * (hammingWeight z : ℂ))) • ket z ∧
    act (collective n pauliZ 2) (ket z) =
      (((n : ℂ) ^ 2 - (n : ℂ) * (4 * (hammingWeight z : ℂ) + 1) +
        4 * (hammingWeight z : ℂ) ^ 2) / 2) • ket z ∧
    act (collective n pauliZ n) (ket z) =
      ((-1 : ℂ) ^ hammingWeight z) • ket z := by sorry

end QAlgorithms.Papers.Independent.Support50.P30

end
