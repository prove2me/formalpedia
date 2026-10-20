-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P12_hamiltonianRigidity
-- name    : QAlgorithms.Papers.Independent.Dependency50.P12.hamiltonianRigidity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:45:38.78879+00:00
-- url     : https://prove2.me/theorems/3c95fb3a-78bd-4990-bd8a-ff72dab3e559
-- title:
--   Corollary 2.17: Hamiltonian rigidity and all four consequences
-- statement:
--   For a positive integer \(d\), operators act on \(\mathbb C^d\). The real ambient LK algebra consists of complex-linear, Hermiticity-preserving, trace-annihilating superoperators, with the composition commutator as bracket. In a Hilbert--Schmidt orthonormal traceless Hermitian basis \(F_j\), physical generators have the GKLS form with Hamiltonian term \(-i[H,\rho]\), half anticommutator, and positive semidefinite Kossakowski matrix \(K\). Write \(W_{\rm GKLS}\) for this cone and call a generator purely Hamiltonian when it equals \(-i[H,\cdot]\) for a traceless Hermitian \(H\).
--
--   Let \(\mathfrak g\subseteq\mathfrak g_{\rm LK}\) be a real Lie subalgebra, \(W\subseteq\mathfrak g\cap W_{\rm GKLS}\) a closed convex cone, and fix a Levi splitting \(\mathfrak g=\mathfrak s\ltimes\mathfrak r\). Then
--   \[
--   W\cap[\mathfrak g,\mathfrak g]\subseteq
--    \{\text{purely Hamiltonian generators in }\mathfrak g\}.
--   \]
--   The same holds for \(W\cap\mathfrak s\); if \(\mathfrak g\) is semisimple, every element of \(W\) is Hamiltonian. For \(\varphi(L)=-\operatorname{Re}\operatorname{Tr}(L)/d\),
--   \[
--   \varphi(X)=\varphi(\pi_{\mathfrak r}X)\quad(X\in\mathfrak g).
--   \]
--   Finally, for arbitrary \(L_1,L_2\in\mathfrak g_{\rm LK}\), their bracket is physical exactly when it is purely Hamiltonian. The commutator ideal means the span of all brackets; the inputs in the final clause need not be physical.
-- source:
--   The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones, arXiv:2608.27330v1, PDF p. 12, Corollary 2.17: Hamiltonian rigidity and all four consequences

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

/-- arXiv:2608.27330v1, PDF pp.12--13, Corollary 2.17, with all four consequences.
A closed convex cone is sufficient; invariance under its edge is not assumed. -/
theorem hamiltonianRigidity {d : ℕ} (hd : 0 < d)
    (F : Fin (d^2-1) → P59.Operator d) (hF : P59.IsTracelessHermitianBasis F)
    (horth : P59.gramMatrix F = 1)
    (g : LieSubalgebra ℝ (Super d)) (hg : ∀ L : g, LK (L : Super d))
    (D : LeviSplitting g) (W : Set g) (hclosed : IsClosed W) (hcone : IsCone W)
    (hphys : ∀ L ∈ W, P59.IsPhysicalAction F (P26.applyMap (L : Super d))) :
    (∀ L ∈ W, L ∈ LieAlgebra.derivedSeries ℝ g 1 →
      Hamiltonian (L : Super d)) ∧
    (∀ L ∈ W, L ∈ D.s → Hamiltonian (L : Super d)) ∧
    (LieAlgebra.radical ℝ g = ⊥ → ∀ L ∈ W, Hamiltonian (L : Super d)) ∧
    (∀ L : g, P59.dissipationStrength (P26.applyMap (L : Super d)) =
      P59.dissipationStrength (P26.applyMap (((piR D L : D.r) : g) : Super d))) ∧
    (∀ L M : Super d, LK L → LK M →
      (P59.IsPhysicalAction F (P26.applyMap ⁅L, M⁆) ↔ Hamiltonian ⁅L, M⁆)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P12

end
