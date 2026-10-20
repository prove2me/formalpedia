-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P12_fullQubit_fibersVary
-- name    : QAlgorithms.Papers.Independent.Dependency50.P12.fullQubit_fibersVary
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:58:50.546329+00:00
-- url     : https://prove2.me/theorems/5e4ae68d-a9db-4492-8ebf-8e8b30d6d79d
-- title:
--   Example 4.15: full qubit GKLS fibers vary and radial maximum
-- statement:
--   For a positive integer \(d\), operators act on \(\mathbb C^d\). The real ambient LK algebra consists of complex-linear, Hermiticity-preserving, trace-annihilating superoperators, with the composition commutator as bracket. In a Hilbert--Schmidt orthonormal traceless Hermitian basis \(F_j\), physical generators have the GKLS form with Hamiltonian term \(-i[H,\rho]\), half anticommutator, and positive semidefinite Kossakowski matrix \(K\). Write \(W_{\rm GKLS}\) for this cone and call a generator purely Hamiltonian when it equals \(-i[H,\cdot]\) for a traceless Hermitian \(H\).
--
--   For the full qubit physical cone, use Bloch affine coordinates \((Q,b)\) and the splitting with traceless \(Q\) as Levi coordinates and \((\lambda I,b)\) as radical coordinates. Every traceless real \(3\times3\) matrix has an admissible lift; its zero radical lift is Hamiltonian exactly when it is antisymmetric. The full fibers vary. For \(t\ge0\), put \(S_t=t\operatorname{diag}(1,1,-2)\). Then
--   \[
--   S_t+\lambda I\ \text{with }b=0\text{ is physical}
--    \iff \lambda\le-4t.
--   \]
--   The feasible set has the attained greatest element \(-4t\), including at \(t=0\). At this endpoint the normalized Pauli Kossakowski matrix is \(\operatorname{diag}(3t,3t,0)\); the zero radical coordinate belongs to the zero-base fiber. This gives a concrete full-cone obstruction to constant fibers.
-- source:
--   The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones, arXiv:2608.27330v1, PDF p. 27, Example 4.15: full qubit GKLS fibers vary and radial maximum

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

/-- arXiv:2608.27330v1, PDF pp.27--28, Example 4.15.
The radial supremum is stated as an attained greatest element, including t=0. -/
theorem fullQubit_fibersVary :
    fullQubitBase = {S : Matrix (Fin 3) (Fin 3) ℝ | S.trace = 0} ∧
    (∀ S : Matrix (Fin 3) (Fin 3) ℝ, S.trace = 0 →
      (Hamiltonian (blochLift S 0) ↔ S.transpose = -S)) ∧
    (∃ S ∈ fullQubitBase, ∃ T ∈ fullQubitBase, fullQubitFiber S ≠ fullQubitFiber T) ∧
    (∀ t : ℝ, 0 ≤ t →
      (∀ a : ℝ, P59.IsPhysicalAction pauliBasis (P26.applyMap (blochLift (radialBase t + a • 1) 0)) ↔ a ≤ -4*t) ∧
      IsGreatest {a : ℝ | P59.IsPhysicalAction pauliBasis (P26.applyMap (blochLift (radialBase t + a • 1) 0))} (-4*t) ∧
      pauliKossakowskiMatrix (blochLift (radialBase t + (-4*t) • 1) 0) =
        (Matrix.diagonal ![(3*t : ℝ), 3*t, 0]).map Complex.ofReal) ∧
    (0 : ℝ × (Fin 3 → ℝ)) ∈ fullQubitFiber 0 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P12

end
