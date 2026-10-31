-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P28_traceProductJoint
-- name    : QAlgorithms.Papers.Independent.Intake100.P28.traceProductJoint
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:38:55.050529+00:00
-- url     : https://prove2.me/theorems/d09ed473-c47c-4ff0-84e1-0eb1e1f4dd10
-- title:
--   Unnumbered trace-product conclusion (5.5) and concave counterpart
-- statement:
--   Let $n\ge1$, and let spectral zero powers mean the identity. For real $p,r$, define $T_{p,r}(A,B)=\operatorname{Tr}(A^pB^{1-r})$ on the indicated domains. Then
--   $$
--   1\le r\le p\le2:\quad T_{p,r}\text{ is jointly convex on }A\ge0,B>0;
--   $$
--   $$
--   0\le p\le r\le1:\quad T_{p,r}\text{ is jointly concave on }A,B\ge0.
--   $$
--   Equivalently, its Jensen inequality holds for every common mixture weight in $[0,1]$, with the reverse inequality in the concave range.
--
--   This is equation (5.5) and its concave counterpart, reproduced from Bekjan [3]. The nonnegative-exponent range legitimately includes $p=0$ because this trace product contains no division by $p$.
-- source:
--   A Minkowski Type Trace Inequality and Strong Subadditivity of Quantum Entropy II: Convexity and Concavity, arXiv:0710.4167v3, PDF p. 15, Unnumbered trace-product conclusion (5.5) and concave counterpart

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P28

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P35
  (spectralPower tr leftMarginal rightMarginal marginalAC)

namespace QAlgorithms.Papers.Independent.Intake100.P28

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Equation (5.5) and concave counterpart, PDF pp.15–16, Bekjan [3].
Negative powers require a definite second factor. The nonnegative-power branch
includes p=0; this does not define Phi at p=0. -/
theorem traceProductJoint {n : ℕ} (hn : 0 < n) (p r : ℝ) :
    (1 ≤ r → r ≤ p → p ≤ 2 →
      ConvexOn ℝ (regularPairs (Fin n)) (traceProduct p r)) ∧
    (0 ≤ p → p ≤ r → r ≤ 1 →
      ConcaveOn ℝ (psdPairs (Fin n)) (traceProduct p r)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P28

end
