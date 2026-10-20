-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P12_ambient_nonreductive
-- name    : QAlgorithms.Papers.Independent.Dependency50.P12.ambient_nonreductive
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:43:14.465865+00:00
-- url     : https://prove2.me/theorems/452fa228-b232-4ffd-9f2c-238c48926436
-- title:
--   Corollary 2.6: non-reductivity of the ambient algebra
-- statement:
--   For a positive integer \(d\), operators act on \(\mathbb C^d\). The real ambient LK algebra consists of complex-linear, Hermiticity-preserving, trace-annihilating superoperators, with the composition commutator as bracket. In a Hilbert--Schmidt orthonormal traceless Hermitian basis \(F_j\), physical generators have the GKLS form with Hamiltonian term \(-i[H,\rho]\), half anticommutator, and positive semidefinite Kossakowski matrix \(K\). Write \(W_{\rm GKLS}\) for this cone and call a generator purely Hamiltonian when it equals \(-i[H,\cdot]\) for a traceless Hermitian \(H\).
--
--   For \(d\ge2\), write \(n=d^2-1=\dim\mathcal H_0\) and use the source's affine model \(\mathfrak g_{\rm LK}\cong\mathfrak{aff}(\mathbb R^n)\). The radical, center, and nilradical satisfy
--   \[
--   \operatorname{rad}(\mathfrak g_{\rm LK})
--    =\mathbb R I\ltimes\mathbb R^n,\qquad
--   Z(\mathfrak g_{\rm LK})=0,\qquad
--   \operatorname{nil}(\mathfrak g_{\rm LK})=\mathbb R^n.
--   \]
--   Thus the radical differs from the center. The semidirect action is retained explicitly: \([I,T]=T\) for every translation \(T\). This is the non-reductivity conclusion in affine coordinates.
-- source:
--   The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones, arXiv:2608.27330v1, PDF p. 8, Corollary 2.6: non-reductivity of the ambient algebra

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

/-- arXiv:2608.27330v1, PDF p.8, Corollary 2.6, in the affine coordinates of
Theorem 2.5, with dim H0=d^2-1. The proof's nilradical identification is retained. -/
theorem ambient_nonreductive (d : ℕ) (hd : 2 ≤ d) :
    (LieAlgebra.radical ℝ (affineAlgebra (d^2-1)) : Set (affineAlgebra (d^2-1))) =
      affineRadical (d^2-1) ∧
    {X : affineAlgebra (d^2-1) | ∀ Y : affineAlgebra (d^2-1), ⁅X,Y⁆ = 0} = {0} ∧
    ((nilradical : LieIdeal ℝ (affineAlgebra (d^2-1))) : Set (affineAlgebra (d^2-1))) =
      affineTranslations (d^2-1) ∧
    (LieAlgebra.radical ℝ (affineAlgebra (d^2-1)) : Set (affineAlgebra (d^2-1))) ≠
      {X : affineAlgebra (d^2-1) | ∀ Y : affineAlgebra (d^2-1), ⁅X,Y⁆ = 0} ∧
    (∀ T ∈ affineTranslations (d^2-1), ⁅affineIdentity (d^2-1),T⁆ = T) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P12

end
