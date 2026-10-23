-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_invariantDissipator_singleField
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.invariantDissipator_singleField
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:36:58.135991+00:00
-- url     : https://prove2.me/theorems/9467e721-c9b6-432a-b805-050d77ec0969
-- title:
--   Corollary 5.12: Unitary-invariant dissipator prevents generic accessibility
-- statement:
--   Suppose the non-Hamiltonian part of a GKSL generator on $\mathbb C^n$, $n\ge2$, commutes with every unitary conjugation. Then
--
--   $$\mathcal L=\{A\},\qquad A(P\lambda)=P(A\lambda)\quad\text{for every coordinate permutation }P.$$
--
--   If $n>2$, the reduced system is nowhere directly accessible. No separate unitality assumption is added, and covariance concerns the superoperator rather than a chosen jump list.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 27, Corollary 5.12: Unitary-invariant dissipator prevents generic accessibility

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

namespace QAlgorithms.Papers.Independent.Dependency50.P16

local notation "Mat" => fun n : ℕ => Matrix (Fin n) (Fin n) ℂ

local notation "Vec" => fun n : ℕ => Fin n → ℝ

local notation "Hilbert" => fun n : ℕ => EuclideanSpace ℂ (Fin n)

local notation "Operator" => fun n : ℕ => Module.End ℂ (Mat n)

/-- arXiv:2308.00561v1, PDF p.27, Corollary 5.12: Unitary-invariant dissipator prevents generic accessibility.  -/
theorem invariantDissipator_singleField {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n)
    (h : invariantDissipator D) :
    (∃ A : RMat n, fields D = {A} ∧ ∀ p : Equiv.Perm (Fin n),
      ∀ x : Vec n, A *ᵥ (fun i => x (p i)) = fun i => (A *ᵥ x) (p i)) ∧
    (2 < n → nowhereDirectlyAccessible D) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
