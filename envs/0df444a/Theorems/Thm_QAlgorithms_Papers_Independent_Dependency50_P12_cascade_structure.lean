-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P12_cascade_structure
-- name    : QAlgorithms.Papers.Independent.Dependency50.P12.cascade_structure
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:59:59.792551+00:00
-- url     : https://prove2.me/theorems/fdaec0e5-5026-4765-b192-aaaefe62ca79
-- title:
--   §4.6.1 / Appendix A.5: cascaded qutrit algebra and wedge
-- statement:
--   For a positive integer \(d\), operators act on \(\mathbb C^d\). The real ambient LK algebra consists of complex-linear, Hermiticity-preserving, trace-annihilating superoperators, with the composition commutator as bracket. In a Hilbert--Schmidt orthonormal traceless Hermitian basis \(F_j\), physical generators have the GKLS form with Hamiltonian term \(-i[H,\rho]\), half anticommutator, and positive semidefinite Kossakowski matrix \(K\). Write \(W_{\rm GKLS}\) for this cone and call a generator purely Hamiltonian when it equals \(-i[H,\cdot]\) for a traceless Hermitian \(H\).
--
--   For a qutrit, declare the jumps \(|1\rangle\langle2|\) and \(|2\rangle\langle3|\) independently actuable, with unit representatives \(L_1,L_2\) for their dissipative superoperators, and set \(L_3=[L_1,L_2]\). Then
--   \[
--   \mathfrak g=\operatorname{span}_{\mathbb R}\{L_1,L_2,L_3\},\quad
--   \dim\mathfrak g=3,\quad
--   [L_1,L_3]=-L_3,\quad [L_2,L_3]=L_3\ne0.
--   \]
--   The algebra admits a common triangular Liouville basis, its derived series terminates after two steps, and its nonzero lower central series stabilizes after the first step, so it is solvable but not nilpotent. Its Levi factor is zero and its radical is all of \(\mathfrak g\). The local wedge is precisely \(\{\alpha L_1+\beta L_2:\alpha,\beta\ge0\}\), with zero edge and singleton quotient base. For every positive simultaneous pair of rates and every initial density matrix, the resulting evolution converges to \(|1\rangle\langle1|\). This limiting assertion concerns that selected drift.
-- source:
--   The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones, arXiv:2608.27330v1, PDF p. 31, §4.6.1 / Appendix A.5: cascaded qutrit algebra and wedge

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

/-- arXiv:2608.27330v1, PDF pp.31--32,45--46, cascaded qutrit example.
The source's algebraic identities use unit ray representatives. The asymptotic
claim concerns positive simultaneous rates and every initial density matrix. -/
theorem cascade_structure :
    (let L1 : Super 3 := dissipatorMap (Matrix.single 0 1 1)
     let L2 : Super 3 := dissipatorMap (Matrix.single 1 2 1)
     let L3 := ⁅L1, L2⁆
     let g := LieSubalgebra.lieSpan ℝ (Super 3) cascadeG
     Module.finrank ℝ g = 3 ∧
     (g : Set (Super 3)) = (Submodule.span ℝ {L1,L2,L3} : Set (Super 3)) ∧
     (∃ P Q : Super 3, P*Q = 1 ∧ Q*P = 1 ∧
       ∀ L ∈ g, ∀ p q : Fin 3 × Fin 3,
         p.1.val*3+p.2.val < q.1.val*3+q.2.val → (Q*L*P) p q = 0) ∧
     L3 ≠ 0 ∧ ⁅L1,L3⁆ = -L3 ∧ ⁅L2,L3⁆ = L3 ∧
     LieAlgebra.IsSolvable g ∧
     Module.finrank ℝ (LieAlgebra.derivedSeries ℝ g 1) = 1 ∧
     (∀ k : ℕ, 1 ≤ k →
       LieModule.lowerCentralSeries ℝ g g k = LieModule.lowerCentralSeries ℝ g g 1) ∧
     LieModule.lowerCentralSeries ℝ g g 1 ≠ ⊥ ∧
     LieAlgebra.derivedSeries ℝ g 2 = ⊥ ∧
     LieAlgebra.radical ℝ g = ⊤ ∧
     minimalWedge cascadeG = {X | ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ X = a • L1 + b • L2} ∧
     edge (minimalWedge cascadeG) = {0} ∧
     (∀ D : LeviSplitting g, D.s = ⊥ ∧
       quotientCone D {X : g | (X : Super 3) ∈ minimalWedge cascadeG} = {0} ∧
       (∀ R : D.r, R ∈ radicalSlice D {X : g | (X : Super 3) ∈ minimalWedge cascadeG} ↔
         ((R : g) : Super 3) ∈ minimalWedge cascadeG) ∧
       FCC D {X : g | (X : Super 3) ∈ minimalWedge cascadeG})) ∧
    (∀ a b : ℝ, 0 < a → 0 < b → ∀ rho : P59.Operator 3,
      rho.PosSemidef → rho.trace = 1 →
      Filter.Tendsto (fun t : ℝ => P26.applyMap (NormedSpace.exp (t • cascadeDrift a b)) rho)
        Filter.atTop (nhds (Matrix.single 0 0 1))) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P12

end
