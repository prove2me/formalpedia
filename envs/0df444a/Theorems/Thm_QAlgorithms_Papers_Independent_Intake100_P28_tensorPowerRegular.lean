-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P28_tensorPowerRegular
-- name    : QAlgorithms.Papers.Independent.Intake100.P28.tensorPowerRegular
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:32:50.713922+00:00
-- url     : https://prove2.me/theorems/a8b6a3fa-3d14-4394-aff1-acf5096b21b8
-- title:
--   Lemma 2.4: well-defined regular convexity and concavity
-- statement:
--   Let $n\ge1$, and write $A^p\otimes B^{1-r}$ for ordinary spectral powers and the matrix tensor product. Mixtures use $t\in[0,1]$. The following assertions hold in Loewner order:
--   $$
--   1\le r\le p\le2:\quad (A,B)\mapsto A^p\otimes B^{1-r}\ \text{is jointly operator convex on }A\ge0,\ B>0;
--   $$
--   $$
--   0\le p\le r\le1:\quad (A,B)\mapsto A^p\otimes B^{1-r}\ \text{is jointly operator concave on }A,B\ge0.
--   $$
--   Loewner order means that the appropriate Jensen difference is positive semidefinite. The zero spectral exponent denotes the identity, also on a kernel.
--
--   This preserves the well-defined regular convex branch and the whole nonnegative-exponent concave branch of the cited Ando and Lieb results.
-- source:
--   A Minkowski Type Trace Inequality and Strong Subadditivity of Quantum Entropy II: Convexity and Concavity, arXiv:0710.4167v3, PDF p. 9, Lemma 2.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P28

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P35
  (spectralPower tr leftMarginal rightMarginal marginalAC)

namespace QAlgorithms.Papers.Independent.Intake100.P28

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 2.4, PDF pp.9–10: regular convexity and full nonnegative-power
concavity. Ando [1], Corollaries 6.3,6.2, and Lieb [12]. -/
theorem tensorPowerRegular {n : ℕ} (hn : 0 < n) (p r : ℝ) :
    (1 ≤ r → r ≤ p → p ≤ 2 →
      OperatorConvexOn (regularPairs (Fin n)) (tensorPowerPair p r)) ∧
    (0 ≤ p → p ≤ r → r ≤ 1 →
      OperatorConcaveOn (psdPairs (Fin n)) (tensorPowerPair p r)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P28

end
