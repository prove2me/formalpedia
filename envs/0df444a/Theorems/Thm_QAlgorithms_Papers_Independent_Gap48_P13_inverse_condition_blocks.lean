-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P13_inverse_condition_blocks
-- name    : QAlgorithms.Papers.Independent.Gap48.P13.inverse_condition_blocks
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:44:29.788823+00:00
-- url     : https://prove2.me/theorems/2b7d557e-9117-4d91-bccc-e5016f051d37
-- title:
--   Two block identities forced by the inverse condition
-- statement:
--   Let $A>0$ act on a finite-dimensional orthogonal sum $H_1\oplus H_2\oplus H_3$, with blocks $A_{ij}:H_j\to H_i$. Define $B=\operatorname{diag}(A_{12,12},I_{H_3})$, $C=\operatorname{diag}(I_{H_1},A_{22},I_{H_3})$, and $D=\operatorname{diag}(I_{H_1},A_{23,23})$, all expressed on the same three-block space. If
--
--   $$A^{-1}(I+A)D(I+D)^{-1}=B^{-1}(I+B)C(I+C)^{-1},$$
--
--   then both conclusions hold:
--
--   $$A_{13}=A_{12}A_{22}^{-1}A_{23},\qquad A_{13}=A_{12}(A_{22}+I)^{-1}A_{23}.$$
--
--   Positive definiteness specifies the domain of all ordinary inverses in the source. This is only an implication from the displayed matrix identity; it does not assert its converse or assume Markovness.
-- source:
--   Markov triplets on CCR-algebras, arXiv:0812.3724v2, PDF p. 15, Theorem 2.2

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P13

noncomputable section

open Filter MeasureTheory

open scoped BigOperators Topology ENNReal ComplexOrder Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Gap48.P13

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P21 (imaginaryPower)

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]

/-- Theorem 2.2, PDF pp.15–16: premise (42), both conclusions (43).
Positive definiteness states the domain of the ordinary inverses in the source;
no zero-valued singular-matrix inverse or Markov premise is substituted. -/
theorem inverse_condition_blocks (A : Mat (I ⊕ (J ⊕ K))) (hA : A.PosDef)
    (hcondition : A⁻¹ * (1 + A) * dMatrix A * (1 + dMatrix A)⁻¹ =
      (bMatrix A)⁻¹ * (1 + bMatrix A) * cMatrix A * (1 + cMatrix A)⁻¹) :
    a13 A = a12 A * (a22 A)⁻¹ * a23 A ∧
    a13 A = a12 A * (a22 A + 1)⁻¹ * a23 A := by sorry

end QAlgorithms.Papers.Independent.Gap48.P13

end
