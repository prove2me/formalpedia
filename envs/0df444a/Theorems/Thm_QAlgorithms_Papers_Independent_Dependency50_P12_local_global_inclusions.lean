-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P12_local_global_inclusions
-- name    : QAlgorithms.Papers.Independent.Dependency50.P12.local_global_inclusions
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:48:37.122894+00:00
-- url     : https://prove2.me/theorems/663b2c44-3ff2-4b98-82c5-1584dbe9a877
-- title:
--   Unnumbered §3.1: physical/local/global inclusions and possible strictness
-- statement:
--   For a positive integer \(d\), operators act on \(\mathbb C^d\). The real ambient LK algebra consists of complex-linear, Hermiticity-preserving, trace-annihilating superoperators, with the composition commutator as bracket. In a Hilbert--Schmidt orthonormal traceless Hermitian basis \(F_j\), physical generators have the GKLS form with Hamiltonian term \(-i[H,\rho]\), half anticommutator, and positive semidefinite Kossakowski matrix \(K\). Write \(W_{\rm GKLS}\) for this cone and call a generator purely Hamiltonian when it equals \(-i[H,\cdot]\) for a traceless Hermitian \(H\).
--
--   For a finite family \(G\) of independently actuable physical rays, let \(\mathfrak g(G)=\operatorname{Lie}(G)\), let \(W(G)\) be the minimal closed Lie wedge containing it inside \(\mathfrak g(G)\), and let \(\Sigma(G)\) be the ambient closure of finite positive-time products. Its global tangent wedge consists of all \(X\) with \(e^{tX}\in\Sigma(G)\) for every \(t\ge0\). Then
--   \[
--   W(G)\subseteq\mathfrak g(G)\cap W_{\rm GKLS},
--   \qquad W(G)\subseteq L(\Sigma(G)).
--   \]
--   The intersection \(L(\Sigma(G))\cap\mathfrak g(G)\) is a closed Lie wedge containing \(G\). Strictness is witnessed by a single nonzero Hamiltonian direction: locally its wedge is its nonnegative ray, while ambient compact flow closure supplies the negative direction globally. A Pauli-\(z\) qubit Hamiltonian is chosen for this witness.
-- source:
--   The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones, arXiv:2608.27330v1, PDF p. 16, Unnumbered §3.1: physical/local/global inclusions and possible strictness

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

/-- arXiv:2608.27330v1, PDF pp.15--17, Equations (15)--(16) and strictness example.
The singleton Hamiltonian witness is explicit; ambient closure supplies its inverse. -/
theorem local_global_inclusions {d : ℕ} (hd : 0 < d)
    (F : Fin (d^2-1) → P59.Operator d) (hF : P59.IsTracelessHermitianBasis F)
    (horth : P59.gramMatrix F = 1)
    (G : Set (Super d)) (hfinite : G.Finite) (hphys : ∀ L ∈ G, P59.IsPhysicalAction F (P26.applyMap L)) :
    (minimalWedge G ⊆ {L | L ∈ LieSubalgebra.lieSpan ℝ (Super d) G ∧ P59.IsPhysicalAction F (P26.applyMap L)}) ∧
    IsLieWedge (globalTangentWedge G ∩ (LieSubalgebra.lieSpan ℝ (Super d) G : Set (Super d))) ∧
    G ⊆ globalTangentWedge G ∧ minimalWedge G ⊆ globalTangentWedge G ∧
    (let H := coherentMap (sigma 2)
     H ≠ 0 ∧ minimalWedge {H} = {X | ∃ a : ℝ, 0 ≤ a ∧ X = a • H} ∧
       -H ∈ globalTangentWedge {H} ∧ -H ∉ minimalWedge {H}) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P12

end
