-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P12_infinitesimal_FCC
-- name    : QAlgorithms.Papers.Independent.Dependency50.P12.infinitesimal_FCC
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:59:22.463184+00:00
-- url     : https://prove2.me/theorems/706c7705-e9a1-4539-9edd-4b1f4f59744e
-- title:
--   Proposition 4.17: infinitesimal FCC through graph derivative
-- statement:
--   Let \(\mathfrak g\) be a finite-dimensional real Lie algebra with its usual Hausdorff vector-space topology. Fix a Levi splitting \(\mathfrak g=\mathfrak s\ltimes\mathfrak r\), where \(\mathfrak r=\operatorname{rad}(\mathfrak g)\), and identify \((S,R)\) with \(S+R\). For a closed Lie wedge \(W\), write \(E(W)=W\cap(-W)\), \(W_{\mathfrak r}=W\cap\mathfrak r\), \(C=\pi_{\mathfrak s}(W)\), \(F(S)=\{R\in\mathfrak r:S+R\in W\}\), and \(E_{\rm quot}=\pi_{\mathfrak s}(E(W))\). A Lie wedge is a closed convex cone containing zero and invariant under \(e^{\operatorname{ad}X}\) for every \(X\in E(W)\).
--
--   Let \(\Gamma=\{(S,R):S\in C,\ R\in F(S)\}\). For any set \(A\), its contingent cone at \(x\) consists of limits \(a_n(x_n-x)\) with \(x_n\in A\), \(x_n\to x\), and \(a_n>0\). Define \(DF(S\mid R)(V)=\{Q:(V,Q)\in T_{(S,R)}\Gamma\}\). With \(\rho(S)R=[S,R]\), global FCC is equivalent to subtangency under the edge, and at \(X_0=S_0+R_0\in E(W)\), \(S+R\in W\), this is exactly
--   \[
--   [R_0,R]+\rho(S_0)R-\rho(S)R_0
--    \in DF(S\mid R)([S_0,S]).
--   \]
--   The membership also forces \([S_0,S]\in T_SC\). The graph derivative includes perturbed base directions; the printed closed Lie-wedge hypothesis is retained.
-- source:
--   The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones, arXiv:2608.27330v1, PDF p. 29, Proposition 4.17: infinitesimal FCC through graph derivative

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P12

noncomputable section

open scoped Matrix ComplexOrder Matrix.Norms.Frobenius

open Set

namespace QAlgorithms.Papers.Independent.Dependency50.P12

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] Classical.propDecidable Classical.decEq

open Coordinates

section AbstractResults

variable {A : Type*} [LieRing A] [LieAlgebra ℝ A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul ℝ A]
    [T2Space A] [FiniteDimensional ℝ A]

/-- arXiv:2608.27330v1, PDF pp.29--30, Proposition 4.17.
The closed Lie-wedge hypothesis is retained as printed. The radical velocity
uses the two action terms with opposite signs. -/
theorem infinitesimal_FCC (D : LeviSplitting A) (W : Set A)
    (hW : IsLieWedge W) :
    (FCC D W ↔ ∀ X ∈ edge W, ∀ Y ∈ W, ⁅X, Y⁆ ∈ contingent W Y) ∧
    (∀ (S0 S : D.s) (R0 R : D.r),
      (S0 : A) + (R0 : A) ∈ edge W → (S : A) + (R : A) ∈ W →
      (⁅(S0 : A) + (R0 : A), (S : A) + (R : A)⁆ ∈
          contingent W ((S : A) + (R : A)) ↔
        ⁅R0, R⁆ + action D S0 R - action D S R0 ∈
          fiberDerivative D W S R ⁅S0, S⁆)) ∧
    (∀ (S0 S : D.s) (R0 R : D.r),
      (S0 : A) + (R0 : A) ∈ edge W → (S : A) + (R : A) ∈ W →
      ⁅R0, R⁆ + action D S0 R - action D S R0 ∈
        fiberDerivative D W S R ⁅S0, S⁆ ∧
      ⁅S0, S⁆ ∈ contingent (quotientCone D W) S) := by sorry

end AbstractResults

end QAlgorithms.Papers.Independent.Dependency50.P12

end
