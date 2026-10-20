-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P12_four_structural_types
-- name    : QAlgorithms.Papers.Independent.Dependency50.P12.four_structural_types
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:50:57.829435+00:00
-- url     : https://prove2.me/theorems/3f8a3b5d-713f-4da4-afa8-7e536d3deb38
-- title:
--   Unnumbered §3.2: four structural Levi types
-- statement:
--   For a positive integer \(d\), operators act on \(\mathbb C^d\). The real ambient LK algebra consists of complex-linear, Hermiticity-preserving, trace-annihilating superoperators, with the composition commutator as bracket. In a Hilbert--Schmidt orthonormal traceless Hermitian basis \(F_j\), physical generators have the GKLS form with Hamiltonian term \(-i[H,\rho]\), half anticommutator, and positive semidefinite Kossakowski matrix \(K\). Write \(W_{\rm GKLS}\) for this cone and call a generator purely Hamiltonian when it equals \(-i[H,\cdot]\) for a traceless Hermitian \(H\).
--
--   Let \(G\) be a finite family of independently actuable physical rays, let \(\mathfrak g=\operatorname{Lie}(G)\), and let \(W\) be its minimal closed local wedge. Fix \(\mathfrak g=\mathfrak s\ltimes\mathfrak r\). The four structural descriptions cover all cases, allowing overlap of the first two at zero:
--   \[
--   \mathfrak s=0;\quad \mathfrak r=0;\quad
--   \mathfrak s,\mathfrak r\ne0,\ \mathfrak r=Z(\mathfrak g);\quad
--   \mathfrak s,\mathfrak r\ne0,\ \mathfrak r\ne Z(\mathfrak g).
--   \]
--   In the first case the algebra is solvable and every finite complex matrix representation, including a complexified real representation, is simultaneously upper triangular, equivalently has a complete invariant flag. In the second it is semisimple and its physical wedge Hamiltonian-only. In the mixed reductive case the adjoint module is completely reducible and the Levi action is zero, yielding a direct sum. In the mixed non-reductive case a zero Levi action requires a nonabelian radical; in the nonzero-action branch, action coupling occurs exactly when both radical slice and quotient cone are nontrivial. The classification alone asserts no mixing or relaxation.
-- source:
--   The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones, arXiv:2608.27330v1, PDF p. 18, Unnumbered §3.2: four structural Levi types

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

/-- arXiv:2608.27330v1, PDF pp.18--19, Section 3.2, four structural types.
These are conditional descriptions with coverage, not exclusive cases at the
zero algebra. The source makes no mixing, relaxation, or complexity bound claim. -/
theorem four_structural_types {d : ℕ} (hd : 0 < d)
    (F : Fin (d^2-1) → P59.Operator d) (hF : P59.IsTracelessHermitianBasis F)
    (horth : P59.gramMatrix F = 1) (G : Set (Super d)) (hfinite : G.Finite)
    (hphys : ∀ L ∈ G, P59.IsPhysicalAction F (P26.applyMap L))
    (D : LeviSplitting (LieSubalgebra.lieSpan ℝ (Super d) G)) :
    let g := LieSubalgebra.lieSpan ℝ (Super d) G
    let W : Set g := {X | (X : Super d) ∈ minimalWedge G}
    let Z : Set g := {X | ∀ Y : g, ⁅X,Y⁆ = 0}
    (D.s = ⊥ ∨ D.r = ⊥ ∨
      (D.s ≠ ⊥ ∧ D.r ≠ ⊥ ∧ (D.r : Set g) = Z) ∨
      (D.s ≠ ⊥ ∧ D.r ≠ ⊥ ∧ (D.r : Set g) ≠ Z)) ∧
    (D.s = ⊥ → LieAlgebra.IsSolvable g ∧
      ∀ (m : ℕ) (rho : g →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℂ), SimultaneouslyTriangularizable rho) ∧
    (D.r = ⊥ → LieAlgebra.radical ℝ g = ⊥ ∧ ∀ X ∈ W, Hamiltonian (X : Super d)) ∧
    (D.s ≠ ⊥ → D.r ≠ ⊥ → (D.r : Set g) = Z →
      AdjointCompletelyReducible g ∧ ∀ S : D.s, ∀ R : D.r, action D S R = 0) ∧
    (D.s ≠ ⊥ → D.r ≠ ⊥ → (D.r : Set g) ≠ Z →
      ((∀ S : D.s, ∀ R : D.r, action D S R = 0) → ∃ R Q : D.r, ⁅R,Q⁆ ≠ 0) ∧
      ((∃ S : D.s, ∃ R : D.r, action D S R ≠ 0) →
        (ActionCoupled D W ↔ radicalSlice D W ≠ {0} ∧ quotientCone D W ≠ {0}))) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P12

end
