-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P12_twoQubit_edgeAndOrbit
-- name    : QAlgorithms.Papers.Independent.Dependency50.P12.twoQubit_edgeAndOrbit
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:02:38.854298+00:00
-- url     : https://prove2.me/theorems/c0cc0dbb-f8c0-4624-aaa8-9f8565aea565
-- title:
--   §5.2: exact edge and orbit completion
-- statement:
--   For a positive integer \(d\), operators act on \(\mathbb C^d\). The real ambient LK algebra consists of complex-linear, Hermiticity-preserving, trace-annihilating superoperators, with the composition commutator as bracket. In a Hilbert--Schmidt orthonormal traceless Hermitian basis \(F_j\), physical generators have the GKLS form with Hamiltonian term \(-i[H,\rho]\), half anticommutator, and positive semidefinite Kossakowski matrix \(K\). Write \(W_{\rm GKLS}\) for this cone and call a generator purely Hamiltonian when it equals \(-i[H,\cdot]\) for a traceless Hermitian \(H\).
--
--   For the two-qubit specification with controls \(H_{A,i}=\sigma_{A,i}\otimes I_B/2\) of both signs and independently switchable jumps \(P_{A,0}\otimes\sigma_{B,-}\), \(P_{A,1}\otimes\sigma_{B,-}\), let \(\mathfrak g_A\) be the primary control algebra and select a compatible Levi complement containing it. The exact local wedge obeys
--   \[
--   E(W)=\mathfrak g_A\cong\mathfrak{su}(2),\qquad
--   W=\overline{\operatorname{cone}}(\mathfrak g_A\cup\mathcal O_0\cup\mathcal O_1),
--   \]
--   where \(\mathcal O_i\) is the individual \(SU(2)_A\) orbit of the corresponding dissipator. The two rotations are independently chosen. The first orbit-completion output is already the fixed wedge. The Levi factor has dimension nine, the edge dimension three, and the quotient cone strictly contains the projected control edge. Full FCC holds, and its zero-base consequence preserves the radical slice under the controls. Individual orbit dissipators are not placed in the radical slice.
-- source:
--   The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones, arXiv:2608.27330v1, PDF p. 35, §5.2: exact edge and orbit completion

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

/-- arXiv:2608.27330v1, PDF pp.35--37, Section 5.2.
The compatible Levi complement is selected as in Section 5.1. The two orbit
variables are independent; the orbit cones are not placed in the radical slice. -/
theorem twoQubit_edgeAndOrbit
    (D : LeviSplitting (LieSubalgebra.lieSpan ℝ (Super 4) twoQubitG))
    (hcompat : ∀ X : LieSubalgebra.lieSpan ℝ (Super 4) twoQubitG,
      (X : Super 4) ∈ twoQubitControl → X ∈ D.s) :
    let g := LieSubalgebra.lieSpan ℝ (Super 4) twoQubitG
    let W : Set g := {X | (X : Super 4) ∈ minimalWedge twoQubitG}
    edge (minimalWedge twoQubitG) = (twoQubitControl : Set (Super 4)) ∧
    Module.finrank ℝ twoQubitControl = 3 ∧ Module.finrank ℝ D.s = 9 ∧
    minimalWedge twoQubitG = closedConicalHull
      ((twoQubitControl : Set (Super 4)) ∪ modulatedOrbit 0 ∪ modulatedOrbit 1) ∧
    wedgeStage twoQubitG 1 = minimalWedge twoQubitG ∧
    wedgeStage twoQubitG 2 = wedgeStage twoQubitG 1 ∧
    piS D '' {X : g | (X : Super 4) ∈ twoQubitControl} ⊂ quotientCone D W ∧
    FCC D W ∧
    (∀ X : g, (X : Super 4) ∈ twoQubitControl →
      expAd X '' ((fun R : D.r => (R : g)) '' radicalSlice D W) ⊆
        ((fun R : D.r => (R : g)) '' radicalSlice D W)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P12

end
