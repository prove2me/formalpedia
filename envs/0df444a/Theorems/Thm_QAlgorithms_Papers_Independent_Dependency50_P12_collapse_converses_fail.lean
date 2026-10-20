-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P12_collapse_converses_fail
-- name    : QAlgorithms.Papers.Independent.Dependency50.P12.collapse_converses_fail
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:58:14.31312+00:00
-- url     : https://prove2.me/theorems/7b38af29-d28c-4eb0-b9ac-1faff0c9b319
-- title:
--   Remark 4.14: two reductive counterexamples to collapse converses
-- statement:
--   For a positive integer \(d\), operators act on \(\mathbb C^d\). The real ambient LK algebra consists of complex-linear, Hermiticity-preserving, trace-annihilating superoperators, with the composition commutator as bracket. In a Hilbert--Schmidt orthonormal traceless Hermitian basis \(F_j\), physical generators have the GKLS form with Hamiltonian term \(-i[H,\rho]\), half anticommutator, and positive semidefinite Kossakowski matrix \(K\). Write \(W_{\rm GKLS}\) for this cone and call a generator purely Hamiltonian when it equals \(-i[H,\cdot]\) for a traceless Hermitian \(H\).
--
--   Work in the reductive algebra \(\mathfrak{su}(2)\oplus\mathbb RD\), with central nonzero depolarizing direction \(D\), and choose the pointed Lie-generating Hamiltonian cone \(C=\operatorname{cone}\{L_x,L_y,L_z\}\). First, \(W_1=C+\mathbb R_{\ge0}D\) is a Lie wedge with zero edge, base \(C\), and constant fibers \(\mathbb R_{\ge0}D\), although \(C\not\subseteq E(W_1)\). Second, let
--   \[
--   W_2=\operatorname{cone}\{L_x,L_y,L_z,L_x+2D\}.
--   \]
--   This is a closed polyhedral Lie wedge with zero edge, base \(C\subseteq W_2\), and zero radical slice. Its fiber over \(L_x\) contains \([0,2]D\), whereas its zero fiber is \(\{0\}\). Thus its fibers vary. These concrete choices witness the two distinct failures of converse or weakening.
-- source:
--   The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones, arXiv:2608.27330v1, PDF p. 27, Remark 4.14: two reductive counterexamples to collapse converses

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

/-- arXiv:2608.27330v1, PDF p.27, Remark 4.14, both counterexamples.
The chosen three positive Pauli directions instantiate the paper's pointed
Lie-generating cone; the central direction is the pauliDepolarizingGenerator generator. -/
theorem collapse_converses_fail :
    IsLieWedge constantCounterexample ∧ edge constantCounterexample = {0} ∧
    depolarizingProjection '' constantCounterexample = pointedHamiltonianCone ∧
    (∀ S ∈ pointedHamiltonianCone, centralFiber constantCounterexample S = Set.Ici 0) ∧
    ¬ pointedHamiltonianCone ⊆ edge constantCounterexample ∧
    IsLieWedge varyingCounterexample ∧ PolyhedralCone varyingCounterexample ∧
    edge varyingCounterexample = {0} ∧
    depolarizingProjection '' varyingCounterexample = pointedHamiltonianCone ∧
    pointedHamiltonianCone ⊆ varyingCounterexample ∧
    centralFiber varyingCounterexample 0 = {0} ∧
    Set.Icc 0 2 ⊆ centralFiber varyingCounterexample (coherentMap (sigma 0)) ∧
    centralFiber varyingCounterexample (coherentMap (sigma 0)) ≠ centralFiber varyingCounterexample 0 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P12

end
