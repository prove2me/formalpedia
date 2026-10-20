-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P12_depolarizing_structure
-- name    : QAlgorithms.Papers.Independent.Dependency50.P12.depolarizing_structure
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:00:39.933242+00:00
-- url     : https://prove2.me/theorems/b921d918-d2ab-4cd0-826a-14ddb697d0d2
-- title:
--   §4.6.2: full-control depolarizing qubit
-- statement:
--   For a positive integer \(d\), operators act on \(\mathbb C^d\). The real ambient LK algebra consists of complex-linear, Hermiticity-preserving, trace-annihilating superoperators, with the composition commutator as bracket. In a Hilbert--Schmidt orthonormal traceless Hermitian basis \(F_j\), physical generators have the GKLS form with Hamiltonian term \(-i[H,\rho]\), half anticommutator, and positive semidefinite Kossakowski matrix \(K\). Write \(W_{\rm GKLS}\) for this cone and call a generator purely Hamiltonian when it equals \(-i[H,\cdot]\) for a traceless Hermitian \(H\).
--
--   For a qubit, use bidirectional controls \(L_i=-i[\sigma_i,\cdot]\) and an independently switchable depolarizing ray \(D=\sum_i(\sigma_i\,\cdot\,\sigma_i-\mathrm{id})\). The control algebra is \(\mathfrak{su}(2)\), \([L_x,L_y]=2L_z\) cyclically, and \(D\) commutes with every control. Thus
--   \[
--   \mathfrak g=\mathfrak{su}(2)\oplus\mathbb RD,\quad
--   W=\{S+\alpha D:S\in\mathfrak{su}(2),\ \alpha\ge0\},\quad
--   E(W)=\mathfrak{su}(2).
--   \]
--   The radical equals the central line \(\mathbb RD\), and every control-base fiber is the same nonnegative radical ray. Every positive rate \(\gamma\) gives the same pair of generated algebra and local wedge. Its selected depolarizing drift has Bloch part \(-4\gamma I\) and sends every density matrix to \(I/2\) asymptotically.
-- source:
--   The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones, arXiv:2608.27330v1, PDF p. 32, §4.6.2: full-control depolarizing qubit

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

/-- arXiv:2608.27330v1, PDF p.32, Section 4.6.2, full-control pauliDepolarizingGenerator qubit.
The Hamiltonians are sigma_i, so [L_x,L_y]=2 L_z. The radical ray and limiting
behavior retain the positive noise rate. -/
theorem depolarizing_structure :
    Module.finrank ℝ qubitControl = 3 ∧ LieAlgebra.radical ℝ qubitControl = ⊥ ∧
    ⁅coherentMap (sigma 0), coherentMap (sigma 1)⁆ = 2 • coherentMap (sigma 2) ∧
    ⁅coherentMap (sigma 1), coherentMap (sigma 2)⁆ = 2 • coherentMap (sigma 0) ∧
    ⁅coherentMap (sigma 2), coherentMap (sigma 0)⁆ = 2 • coherentMap (sigma 1) ∧
    (∀ S ∈ qubitControl, ⁅S, pauliDepolarizingGenerator⁆ = 0) ∧
    (let g := LieSubalgebra.lieSpan ℝ (Super 2) (depolarizingG 1)
     (g : Set (Super 2)) = {X | ∃ S ∈ qubitControl, ∃ a : ℝ, X = S + a • pauliDepolarizingGenerator} ∧
     (LieAlgebra.radical ℝ g : Set g) = {X : g | ∃ a : ℝ, (X : Super 2) = a • pauliDepolarizingGenerator} ∧
     (∀ X : g, X ∈ LieAlgebra.radical ℝ g ↔ ∀ Y : g, ⁅X,Y⁆ = 0)) ∧
    minimalWedge (depolarizingG 1) =
      {X | ∃ S ∈ qubitControl, ∃ a : ℝ, 0 ≤ a ∧ X = S + a • pauliDepolarizingGenerator} ∧
    edge (minimalWedge (depolarizingG 1)) = (qubitControl : Set (Super 2)) ∧
    (∀ S ∈ qubitControl, depolarizingFiber S = {a : ℝ | 0 ≤ a}) ∧
    (∀ gamma : ℝ, 0 < gamma →
      minimalWedge (depolarizingG gamma) = minimalWedge (depolarizingG 1) ∧
      LieSubalgebra.lieSpan ℝ (Super 2) (depolarizingG gamma) =
        LieSubalgebra.lieSpan ℝ (Super 2) (depolarizingG 1) ∧
      blochQ (gamma • pauliDepolarizingGenerator) = (-4*gamma) • 1 ∧
      ∀ rho : P59.Operator 2, rho.PosSemidef → rho.trace = 1 →
        Filter.Tendsto (fun t : ℝ => P26.applyMap (NormedSpace.exp (t • (gamma • pauliDepolarizingGenerator))) rho)
          Filter.atTop (nhds ((2⁻¹ : ℂ) • (1 : P59.Operator 2)))) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P12

end
