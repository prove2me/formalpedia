-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P12_finite_edgeOrbit_construction
-- name    : QAlgorithms.Papers.Independent.Dependency50.P12.finite_edgeOrbit_construction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:49:50.152817+00:00
-- url     : https://prove2.me/theorems/ee338167-72ab-49c1-a969-29b242e0d77b
-- title:
--   Proposition 3.5: exact finite edge-orbit construction
-- statement:
--   For a positive integer \(d\), operators act on \(\mathbb C^d\). The real ambient LK algebra consists of complex-linear, Hermiticity-preserving, trace-annihilating superoperators, with the composition commutator as bracket. In a Hilbert--Schmidt orthonormal traceless Hermitian basis \(F_j\), physical generators have the GKLS form with Hamiltonian term \(-i[H,\rho]\), half anticommutator, and positive semidefinite Kossakowski matrix \(K\). Write \(W_{\rm GKLS}\) for this cone and call a generator purely Hamiltonian when it equals \(-i[H,\cdot]\) for a traceless Hermitian \(H\).
--
--   For a finite declared physical generator family \(G\), the minimal closed Lie wedge \(W(G)\) inside \(\operatorname{Lie}(G)\) exists. The family of containing closed Lie wedges is nonempty and stable under arbitrary intersections. Start with \(W_0=\overline{\operatorname{cone}}G\), set \(E_k=W_k\cap(-W_k)\), and form \(W_{k+1}\) as the closed conical hull of the orbit of \(W_k\) under all finite products of \(e^{\operatorname{ad}X}\), \(X\in E_k\). The edges increase, and at some finite index
--   \[
--   E_{k+1}=E_k,\qquad
--   W_{k+2}=W_{k+1}=W(G)\subseteq L(\Sigma(G)).
--   \]
--   The output \(W_{k+1}\) is a Lie wedge even if the cone enlarged at that first equality step. This is an exact abstract construction, without an effective computational complexity bound.
-- source:
--   The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones, arXiv:2608.27330v1, PDF p. 16, Proposition 3.5: exact finite edge-orbit construction

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

/-- arXiv:2608.27330v1, PDF pp.15--17, Proposition 3.5.
There is no effective runtime or query bound. The first edge-equality step can
enlarge the cone, so its OUTPUT, not its input, is identified with W(G). -/
theorem finite_edgeOrbit_construction {d : ℕ} (hd : 0 < d)
    (F : Fin (d^2-1) → P59.Operator d) (hF : P59.IsTracelessHermitianBasis F)
    (horth : P59.gramMatrix F = 1)
    (G : Set (Super d)) (hfinite : G.Finite) (hphys : ∀ L ∈ G, P59.IsPhysicalAction F (P26.applyMap L)) :
    (∃ V : Set (Super d), IsLieWedge V ∧ G ⊆ V) ∧
    (∀ K : Set (Set (Super d)),
      (∀ V ∈ K, IsLieWedge V ∧ G ⊆ V) →
      IsLieWedge (⋂₀ K) ∧ G ⊆ ⋂₀ K) ∧
    (IsLieWedge (minimalWedge G) ∧ G ⊆ minimalWedge G ∧
      minimalWedge G ⊆ (LieSubalgebra.lieSpan ℝ (Super d) G : Set (Super d)) ∧
      ∀ V : Set (Super d), IsLieWedge V → G ⊆ V → minimalWedge G ⊆ V) ∧
    (∀ k : ℕ, edge (wedgeStage G k) ⊆ edge (wedgeStage G (k+1))) ∧
    (∃ k : ℕ, edge (wedgeStage G (k+1)) = edge (wedgeStage G k) ∧
      IsLieWedge (wedgeStage G (k+1)) ∧
      wedgeStage G (k+2) = wedgeStage G (k+1) ∧
      wedgeStage G (k+1) = minimalWedge G) ∧
    minimalWedge G ⊆ globalTangentWedge G := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P12

end
