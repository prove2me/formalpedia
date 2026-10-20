-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P12_twoQubit_exactStructure
-- name    : QAlgorithms.Papers.Independent.Dependency50.P12.twoQubit_exactStructure
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:01:29.3761+00:00
-- url     : https://prove2.me/theorems/0d915ef5-ed3f-4ca7-9510-80d6e195db59
-- title:
--   §5.1: exact 22/13/9 two-qubit Levi structure
-- statement:
--   For a positive integer \(d\), operators act on \(\mathbb C^d\). The real ambient LK algebra consists of complex-linear, Hermiticity-preserving, trace-annihilating superoperators, with the composition commutator as bracket. In a Hilbert--Schmidt orthonormal traceless Hermitian basis \(F_j\), physical generators have the GKLS form with Hamiltonian term \(-i[H,\rho]\), half anticommutator, and positive semidefinite Kossakowski matrix \(K\). Write \(W_{\rm GKLS}\) for this cone and call a generator purely Hamiltonian when it equals \(-i[H,\cdot]\) for a traceless Hermitian \(H\).
--
--   Use bidirectional controls \(H_{A,i}=\sigma_{A,i}\otimes I_B/2\) and two independently actuable jumps \(J_0=P_{A,0}\otimes\sigma_{B,-}\), \(J_1=P_{A,1}\otimes\sigma_{B,-}\), with \(\sigma_-=|1\rangle\langle0|\). Form the 22 recursive superoperator words of Equation (54), using \(D=D_{J_0}\) and \(E=2D_{J_1}\). They are linearly independent and span the generated algebra; the final word escapes the preceding span. For its radical and a compatible selected Levi complement,
--   \[
--   \dim\mathfrak g=22,\qquad \dim\mathfrak r=13,\qquad \dim\mathfrak s=9.
--   \]
--   The radical has derived dimensions \(13\to12\to0\) and lower-central dimensions \(13\to12\to12\). The complement contains the primary three-dimensional control algebra. Its quotient control action is three copies of the standard adjoint rotation module and has no fixed vector. The actual dissipator \(D_{\sigma_{A,z}\otimes\sigma_{B,-}}\) belongs to the radical but does not commute with the \(x\) control, so the Levi action is nontrivial and the algebra non-reductive. The numerical minors are proof certificates, not hypotheses.
-- source:
--   The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones, arXiv:2608.27330v1, PDF p. 33, §5.1: exact 22/13/9 two-qubit Levi structure

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

/-- arXiv:2608.27330v1, PDF pp.33--35, Section 5.1, exact 22/13/9 structure.
Certificate matrices are not hypotheses. The actual 22 words are a basis; radical
membership and the three-adjoint-copy quotient are conclusions. The numerical
minor values are proof certificates, not additional input assumptions. -/
theorem twoQubit_exactStructure :
    let g := LieSubalgebra.lieSpan ℝ (Super 4) twoQubitG
    let r := LieAlgebra.radical ℝ g
    Module.finrank ℝ g = 22 ∧ Module.finrank ℝ r = 13 ∧
    LinearIndependent ℝ twoQubitWords ∧
    Submodule.span ℝ (Set.range twoQubitWords) = g.toSubmodule ∧
    twoQubitWords 21 ∉ Submodule.span ℝ (twoQubitWords '' {i : Fin 22 | i.val < 21}) ∧
    Module.finrank ℝ (LieAlgebra.derivedSeries ℝ r 1) = 12 ∧
    LieAlgebra.derivedSeries ℝ r 2 = ⊥ ∧
    Module.finrank ℝ (LieModule.lowerCentralSeries ℝ r r 1) = 12 ∧
    LieModule.lowerCentralSeries ℝ r r 2 = LieModule.lowerCentralSeries ℝ r r 1 ∧
    (∀ i : Fin 3, coherentMap (twoQubitH i) ∈ g) ∧
    (∃ R : g, (R : Super 4) = dissipatorMap (tensor2 (sigma 2) sigmaMinus) ∧
      R ∈ r ∧ ⁅coherentMap (twoQubitH 0),(R : Super 4)⁆ ≠ 0) ∧
    ((r : Set g) ≠ {X : g | ∀ Y : g, ⁅X,Y⁆ = 0}) ∧
    ∃ D : LeviSplitting g,
      Module.finrank ℝ D.s = 9 ∧
      (∀ X : g, (X : Super 4) ∈ twoQubitControl → X ∈ D.s) ∧
      (∃ S : D.s, ∃ R : D.r, action D S R ≠ 0) ∧
      (∃ T : D.s ≃ₗ[ℝ] (Fin 3 → (Fin 3 → ℝ)),
        ∀ (i : Fin 3) (C : g), (C : Super 4) = coherentMap (twoQubitH i) →
        ∀ S : D.s, T (piS D ⁅C,(S : g)⁆) =
          fun k => (adjointRotations i).mulVec (T S k)) ∧
      (∀ S : D.s,
        (∀ (i : Fin 3) (C : g), (C : Super 4) = coherentMap (twoQubitH i) →
          piS D ⁅C,(S : g)⁆ = 0) → S = 0) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P12

end
