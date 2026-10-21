-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P31_squareRootIndices_bounds
-- name    : QAlgorithms.Papers.Independent.Next46.P31.squareRootIndices_bounds
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:36:17.691788+00:00
-- url     : https://prove2.me/theorems/dfc498e6-f645-42cf-8607-f8e8779b789f
-- title:
--   Unnumbered introduction result: square-root-state coherence alternatives
-- statement:
--   Let $d\ge1$ and let $\rho$ be a positive trace-class operator of trace one on $L^2(\mathbb R^d)$. For $A=X,K$, set $m_A=\operatorname{Tr}(A\rho)$ and assume that the variance $V_A=\operatorname{Tr}(\rho|A-m_A|^2)$ is finite and strictly positive, and that the displayed square-root-state commutators are Hilbert–Schmidt. Equivalently the coordinate products $A_j\sqrt\rho$ have bounded Hilbert–Schmidt realizations; the first products $A_j\rho$ are trace class. Define $C'_A=\|[A,\sqrt\rho]\|_2$, $D'_A=2\sqrt{V_A}$, and $S'_A=C'_A/D'_A$. Then
--
--   $$
--   0\le S'_X,S'_K\le1,\qquad C'_XD'_K\ge\frac12,\qquad C'_KD'_X\ge\frac12.
--   $$
--
--   These are the proposed alternative index bounds. Centering always uses the original state $\rho$, and the source’s printed denominator factor 2 is preserved.
-- source:
--   Decoherence rates for Galilean covariant dynamics, arXiv:0710.1344v2, PDF p. 4, Unnumbered introduction result: square-root-state coherence alternatives

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

/-- Clark, PDF p.4: both square-root-state alternatives on their finite positive
variance domains; both cross inequalities retain the printed weak constant 1/2. -/
theorem squareRootIndices_bounds {I : Type*} {d : ℕ} (hd : 0 < d)
    (b : HilbertBasis I ℂ (EuclideanSchrodinger d)) (rho : (EuclideanSchrodinger d →L[ℂ] EuclideanSchrodinger d))
    (hrho : IsTraceClass rho ∧ IsPositive rho ∧ operatorTrace b rho = 1) (hregular : CanonicallyRegular rho)
    (hX : RootRegular b positionGraph rho) (hK : RootRegular b momentumGraph rho)
    (hvarX : 0 < observableVariance b positionGraph rho)
    (hvarK : 0 < observableVariance b momentumGraph rho) :
    alternativeNumerator b positionGraph rho / alternativeDenominator b positionGraph rho ∈
      Set.Icc (0 : ℝ) 1 ∧
    alternativeNumerator b momentumGraph rho / alternativeDenominator b momentumGraph rho ∈
      Set.Icc (0 : ℝ) 1 ∧
    (1 : ℝ) / 2 ≤ alternativeNumerator b positionGraph rho * alternativeDenominator b momentumGraph rho ∧
    (1 : ℝ) / 2 ≤ alternativeNumerator b momentumGraph rho * alternativeDenominator b positionGraph rho := by sorry

end QAlgorithms.Papers.Independent.Next46.P31

end
