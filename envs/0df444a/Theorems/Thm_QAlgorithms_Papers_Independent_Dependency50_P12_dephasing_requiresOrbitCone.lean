-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P12_dephasing_requiresOrbitCone
-- name    : QAlgorithms.Papers.Independent.Dependency50.P12.dephasing_requiresOrbitCone
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:07:14.240281+00:00
-- url     : https://prove2.me/theorems/c80d4c2b-2720-4f49-83bc-3d80325abf84
-- title:
--   Remark 6.4: reversible x-control requires a dephasing orbit cone
-- statement:
--   For a positive integer \(d\), operators act on \(\mathbb C^d\). The real ambient LK algebra consists of complex-linear, Hermiticity-preserving, trace-annihilating superoperators, with the composition commutator as bracket. In a Hilbert--Schmidt orthonormal traceless Hermitian basis \(F_j\), physical generators have the GKLS form with Hamiltonian term \(-i[H,\rho]\), half anticommutator, and positive semidefinite Kossakowski matrix \(K\). Write \(W_{\rm GKLS}\) for this cone and call a generator purely Hamiltonian when it equals \(-i[H,\cdot]\) for a traceless Hermitian \(H\).
--
--   For a qubit, declare reversible \(x\) control \(L_x=-i[\sigma_x,\cdot]\) and one independent \(z\)-dephasing ray \(D_z=D_{\sigma_z}\). The candidate \(\mathbb RL_x+\mathbb R_{\ge0}D_z\) has edge \(\mathbb RL_x\), but
--   \[
--   e^{(\pi/4)\operatorname{ad}L_x}D_z=D_{\sigma_y}
--   \]
--   is physical and outside that candidate. The required orbit cone is the closed conical hull of \(D_{a\sigma_y+b\sigma_z}\), \(a,b\in\mathbb R\). It is precisely the three-dimensional cone of real positive semidefinite \(2\times2\) Kossakowski blocks on the \(yz\) plane. The convex hull at unit total rate is the trace-one section, a disk. This orbit cone lies in the actual local wedge and differs from its radical slice. The obstruction is departure from the declared cone, not loss of complete positivity.
-- source:
--   The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones, arXiv:2608.27330v1, PDF p. 40, Remark 6.4: reversible x-control requires a dephasing orbit cone

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

/-- arXiv:2608.27330v1, PDF p.40, Remark 6.4.
For H=sigma_x the quarter turn occurs at t=pi/4. The rotated dissipator is
physical; what fails is membership of the declared cone. -/
theorem dephasing_requiresOrbitCone :
    edge dephasingCandidate = {X | ∃ a : ℝ, X = a • coherentMap (sigma 0)} ∧
    expAd ((Real.pi/4) • coherentMap (sigma 0)) (dissipatorMap (sigma 2)) =
      dissipatorMap (sigma 1) ∧
    P59.IsPhysicalAction pauliBasis (P26.applyMap (dissipatorMap (sigma 1))) ∧
    dissipatorMap (sigma 1) ∉ dephasingCandidate ∧ ¬ IsLieWedge dephasingCandidate ∧
    dephasingOrbitCone = {L | ∃ K : Matrix (Fin 2) (Fin 2) ℝ, K.PosSemidef ∧ L = yzNoise K} ∧
    convexHull ℝ fixedDephasingOrbit =
      {L | ∃ K : Matrix (Fin 2) (Fin 2) ℝ, K.PosSemidef ∧ K.trace = 1 ∧ L = yzNoise K} ∧
    Module.finrank ℝ (Submodule.span ℝ dephasingOrbitCone) = 3 ∧
    dephasingOrbitCone ⊆ minimalWedge dephasingG ∧
    dephasingOrbitCone ≠ dephasingRadicalSlice := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P12

end
