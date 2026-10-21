-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P12_ambient_nilradical_obstruction
-- name    : QAlgorithms.Papers.Independent.Dependency50.P12.ambient_nilradical_obstruction
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T14:04:17.970058+00:00
-- url     : https://prove2.me/theorems/da704271-13e8-42ef-9f99-244e15df8410
-- title:
--   Unnumbered §6.1: abelian nilradical and ambient cone obstruction
-- statement:
--   For \(d\ge2\), identify the ambient LK algebra with \(\mathfrak{aff}(\mathcal H_0)\), where \(\mathcal H_0\) is the real traceless Hermitian space of dimension \(d^2-1\). Its nilradical is the abelian translation ideal. Consequently, for every real linear functional \(\xi\) and nilradical elements \(X,Y\),
--   \[
--   [X,Y]=0,\qquad \xi([X,Y])=0.
--   \]
--   All bracket-induced forms therefore vanish. The full ambient algebra admits no pointed generating invariant closed convex cone. This is an obstruction to full algebra invariance, with no assertion of spectral instability or loss of complete positivity.
-- source:
--   The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones, arXiv:2608.27330v1, PDF p. 37, Unnumbered §6.1: abelian nilradical and ambient cone obstruction

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

/-- arXiv:2608.27330v1, PDF pp.37--38, Section 6.1, in its stated affine model.
Bracket-induced forms vanish on the abelian nilradical; the obstruction is full
algebra invariance, without a spectral or CP conclusion. -/
theorem ambient_nilradical_obstruction (d : ℕ) (hd : 2 ≤ d) :
    ((nilradical : LieIdeal ℝ (affineAlgebra (d^2-1))) : Set (affineAlgebra (d^2-1))) =
      affineTranslations (d^2-1) ∧
    (∀ X Y : affineAlgebra (d^2-1), X ∈ nilradical → Y ∈ nilradical → ⁅X,Y⁆ = 0) ∧
    (∀ xi : affineAlgebra (d^2-1) →ₗ[ℝ] ℝ, ∀ X Y : affineAlgebra (d^2-1),
      X ∈ nilradical → Y ∈ nilradical → xi ⁅X,Y⁆ = 0) ∧
    ¬ (∃ W : Set (affineAlgebra (d^2-1)), IsClosed W ∧ IsCone W ∧ edge W = {0} ∧
      (∀ X : affineAlgebra (d^2-1), ∃ Y ∈ W, ∃ Z ∈ W, X = Y-Z) ∧
      ∀ X : affineAlgebra (d^2-1), expAd X '' W ⊆ W) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P12

end
