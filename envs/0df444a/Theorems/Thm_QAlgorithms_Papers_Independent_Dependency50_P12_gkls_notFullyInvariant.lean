-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P12_gkls_notFullyInvariant
-- name    : QAlgorithms.Papers.Independent.Dependency50.P12.gkls_notFullyInvariant
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:44:11.339789+00:00
-- url     : https://prove2.me/theorems/97b6a473-1776-44a9-a1b1-8869b7ed4f40
-- title:
--   Proposition 2.15: GKLS cone is not fully adjoint invariant
-- statement:
--   For a positive integer \(d\), operators act on \(\mathbb C^d\). The real ambient LK algebra consists of complex-linear, Hermiticity-preserving, trace-annihilating superoperators, with the composition commutator as bracket. In a Hilbert--Schmidt orthonormal traceless Hermitian basis \(F_j\), physical generators have the GKLS form with Hamiltonian term \(-i[H,\rho]\), half anticommutator, and positive semidefinite Kossakowski matrix \(K\). Write \(W_{\rm GKLS}\) for this cone and call a generator purely Hamiltonian when it equals \(-i[H,\cdot]\) for a traceless Hermitian \(H\).
--
--   For every \(d\ge2\), the physical cone is not invariant under the full ambient algebra:
--   \[
--   \exists X\in\mathfrak g_{\rm LK},\ \exists L\in W_{\rm GKLS}:
--   e^{\operatorname{ad}X}L\notin W_{\rm GKLS}.
--   \]
--   The conjugating element need not itself be physical. The result holds in every dimension stated by the source.
-- source:
--   The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones, arXiv:2608.27330v1, PDF p. 12, Proposition 2.15: GKLS cone is not fully adjoint invariant

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

/-- arXiv:2608.27330v1, PDF p.12, Proposition 2.15.
The conjugating X ranges over the full ambient LK algebra, not the physical cone. -/
theorem gkls_notFullyInvariant {d : ℕ} (hd : 2 ≤ d)
    (F : Fin (d^2-1) → P59.Operator d) (hF : P59.IsTracelessHermitianBasis F)
    (horth : P59.gramMatrix F = 1) :
    ∃ X L : Super d, LK X ∧ P59.IsPhysicalAction F (P26.applyMap L) ∧ ¬ P59.IsPhysicalAction F (P26.applyMap (expAd X L)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P12

end
