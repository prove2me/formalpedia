-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P12_unitalDissipator_dimensionBoundary
-- name    : QAlgorithms.Papers.Independent.Dependency50.P12.unitalDissipator_dimensionBoundary
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:47:44.327261+00:00
-- url     : https://prove2.me/theorems/24828e4d-f1ff-4303-b65e-b2bc3c44eddd
-- title:
--   Remark 2.18: dimension boundary for unital dissipator witnesses
-- statement:
--   For a positive integer \(d\), operators act on \(\mathbb C^d\). The real ambient LK algebra consists of complex-linear, Hermiticity-preserving, trace-annihilating superoperators, with the composition commutator as bracket. In a Hilbert--Schmidt orthonormal traceless Hermitian basis \(F_j\), physical generators have the GKLS form with Hamiltonian term \(-i[H,\rho]\), half anticommutator, and positive semidefinite Kossakowski matrix \(K\). Write \(W_{\rm GKLS}\) for this cone and call a generator purely Hamiltonian when it equals \(-i[H,\cdot]\) for a traceless Hermitian \(H\).
--
--   A unital dissipator means a physical generator with zero Hamiltonian coordinate and \(L(I)=0\). For qubits, the bracket of every pair of unital dissipators is purely Hamiltonian. In contrast,
--   \[
--   \forall d\ge3,\quad
--   \exists L_1,L_2\ \text{unital dissipators}:
--   [L_1,L_2]\notin W_{\rm GKLS}.
--   \]
--   Arbitrary unital generators with Hamiltonian terms are not substituted for the source's unital dissipators.
-- source:
--   The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones, arXiv:2608.27330v1, PDF p. 13, Remark 2.18: dimension boundary for unital dissipator witnesses

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P12

noncomputable section

open scoped Matrix ComplexOrder Matrix.Norms.Frobenius

open Set

namespace QAlgorithms.Papers.Independent.Dependency50.P12

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] Classical.propDecidable Classical.decEq

open Coordinates

open QAlgorithms.Papers.Independent.Information100

attribute [local instance] QAlgorithms.Papers.Independent.Dependency50.P12.inheritedSubalgebraTopologicalAddGroup

/-- arXiv:2608.27330v1, PDF p.13, Remark 2.18, the two dimension regimes. -/
theorem unitalDissipator_dimensionBoundary
    (F2 : Fin (2^2-1) → P59.Operator 2) (hF2 : P59.IsTracelessHermitianBasis F2)
    (horth2 : P59.gramMatrix F2 = 1) :
    (∀ L M : Super 2, UnitalDissipator F2 L → UnitalDissipator F2 M →
      Hamiltonian ⁅L, M⁆) ∧
    (∀ (d : ℕ), 3 ≤ d → ∀ F : Fin (d^2-1) → P59.Operator d,
      P59.IsTracelessHermitianBasis F → P59.gramMatrix F = 1 →
      ∃ L M : Super d, UnitalDissipator F L ∧ UnitalDissipator F M ∧
        ¬ P59.IsPhysicalAction F (P26.applyMap ⁅L, M⁆)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P12

end
