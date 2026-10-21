-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P31_gaussianCoherence_formula
-- name    : QAlgorithms.Papers.Independent.Next46.P31.gaussianCoherence_formula
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:26:25.148666+00:00
-- url     : https://prove2.me/theorems/7a1143c0-5ac6-42e9-b007-0e612e7e3d3c
-- title:
--   Example 2.3: Gaussian coherence formula
-- statement:
--   On $L^2(\mathbb R)$ consider the operator with Gaussian kernel
--
--   $$
--   \rho(x,y)=\frac{2\sqrt C}{\sqrt\pi}\exp\!\left[-A(x-y)^2-iB(x^2-y^2)-C(x+y)^2-iD(x-y)-E(x+y)-\frac{E^2}{4C}\right],
--   $$
--
--   where $A,B,C,D,E$ are real and $A\ge C>0$. For the normalized commutator length $C_X$, centered anticommutator spread $D_X$, and their quotient $S_X$, defined above,
--
--   $$
--   C_X(\rho)=\frac1{2\sqrt A},\qquad D_X(\rho)=\frac1{2\sqrt C},\qquad S_X(\rho)=\sqrt{\frac CA}.
--   $$
--
--   Thus the Gaussian index depends only on the ratio of the diagonal and off-diagonal width parameters.
-- source:
--   Decoherence rates for Galilean covariant dynamics, arXiv:0710.1344v2, PDF p. 9, Example 2.3: Gaussian coherence formula

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P31

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal NNReal ComplexOrder Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Next46.P31

open QAlgorithms.PeriodicSchrodinger (Position)

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsTraceClass IsPositive operatorTrace)

/-- Clark, PDF pp.4,9, Example 2.3: all three Gaussian coherence formulas,
including the prefactor and centering of the actual specified Gaussian operator. -/
theorem gaussianCoherence_formula {I : Type*} (b : HilbertBasis I ℂ (EuclideanSchrodinger 1))
    (A B C D E : ℝ) (hAC : C ≤ A) (hC : 0 < C) :
    coherenceLength b positionGraph (kernelOperator (gaussianKernel A B C D E)) =
      1 / (2 * Real.sqrt A) ∧
    coherenceSpread b positionGraph (kernelOperator (gaussianKernel A B C D E)) =
      1 / (2 * Real.sqrt C) ∧
    coherenceIndex b positionGraph (kernelOperator (gaussianKernel A B C D E)) =
      Real.sqrt (C / A) := by sorry

end QAlgorithms.Papers.Independent.Next46.P31

end
