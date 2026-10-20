-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P12_constantFibers_hamiltonianBase
-- name    : QAlgorithms.Papers.Independent.Dependency50.P12.constantFibers_hamiltonianBase
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:57:04.262101+00:00
-- url     : https://prove2.me/theorems/1e7d8b65-7fda-480b-bf4c-15ce85c7a646
-- title:
--   Proposition 4.13: non-Hamiltonian base obstructs collapse
-- statement:
--   For a positive integer \(d\), operators act on \(\mathbb C^d\). The real ambient LK algebra consists of complex-linear, Hermiticity-preserving, trace-annihilating superoperators, with the composition commutator as bracket. In a Hilbert--Schmidt orthonormal traceless Hermitian basis \(F_j\), physical generators have the GKLS form with Hamiltonian term \(-i[H,\rho]\), half anticommutator, and positive semidefinite Kossakowski matrix \(K\). Write \(W_{\rm GKLS}\) for this cone and call a generator purely Hamiltonian when it equals \(-i[H,\cdot]\) for a traceless Hermitian \(H\).
--
--   Let \(\mathfrak g\) be a finite-dimensional real Lie algebra with its usual Hausdorff vector-space topology. Fix a Levi splitting \(\mathfrak g=\mathfrak s\ltimes\mathfrak r\), where \(\mathfrak r=\operatorname{rad}(\mathfrak g)\), and identify \((S,R)\) with \(S+R\). For a closed Lie wedge \(W\), write \(E(W)=W\cap(-W)\), \(W_{\mathfrak r}=W\cap\mathfrak r\), \(C=\pi_{\mathfrak s}(W)\), \(F(S)=\{R\in\mathfrak r:S+R\in W\}\), and \(E_{\rm quot}=\pi_{\mathfrak s}(E(W))\). A Lie wedge is a closed convex cone containing zero and invariant under \(e^{\operatorname{ad}X}\) for every \(X\in E(W)\).
--
--   Assume \(W\subseteq W_{\rm GKLS}\). Constant fibers imply
--   \[
--   C\subseteq W\cap\mathfrak s\subseteq
--    \{\text{purely Hamiltonian generators}\}.
--   \]
--   Equivalently, if a base point \(S\in C\) has a nonzero canonical Hermitian Kossakowski matrix, the fibers cannot be constant. Base coordinates are allowed to be unphysical when this test is applied.
-- source:
--   The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones, arXiv:2608.27330v1, PDF p. 27, Proposition 4.13: non-Hamiltonian base obstructs collapse

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

/-- arXiv:2608.27330v1, PDF p.27, Proposition 4.13.
K on a base coordinate is only Hermitian, and need not be positive semidefinite. -/
theorem constantFibers_hamiltonianBase {d : ℕ} (hd : 0 < d)
    (F : Fin (d^2-1) → P59.Operator d) (hF : P59.IsTracelessHermitianBasis F)
    (horth : P59.gramMatrix F = 1)
    (g : LieSubalgebra ℝ (Super d)) (hg : ∀ L : g, LK (L : Super d))
    (D : LeviSplitting g) (W : Set g) (hW : IsLieWedge W)
    (hphys : ∀ L ∈ W, P59.IsPhysicalAction F (P26.applyMap (L : Super d))) :
    ((∀ S ∈ quotientCone D W, fiber D W S = radicalSlice D W) →
      (∀ S ∈ quotientCone D W, (S : g) ∈ W) ∧
      (∀ L ∈ W, L ∈ D.s → Hamiltonian (L : Super d))) ∧
    ((∃ S ∈ quotientCone D W,
      ∃ (H : P59.Operator d) (K : Matrix (Fin (d^2-1)) (Fin (d^2-1)) ℂ),
        H.IsHermitian ∧ K.IsHermitian ∧ K ≠ 0 ∧
        P26.applyMap (((S : D.s) : g) : Super d) = P59.kossakowskiAction F H K) →
      ¬ ∀ S ∈ quotientCone D W, fiber D W S = radicalSlice D W) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P12

end
