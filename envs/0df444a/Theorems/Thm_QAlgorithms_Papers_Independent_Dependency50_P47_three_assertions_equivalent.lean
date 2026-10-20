-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P47_three_assertions_equivalent
-- name    : QAlgorithms.Papers.Independent.Dependency50.P47.three_assertions_equivalent
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:38:44.753029+00:00
-- url     : https://prove2.me/theorems/baddc71e-dbcb-4a13-a4c2-5b438d69ab18
-- title:
--   Theorem 3(a): three equivalent universal assertions
-- statement:
--   The following are universal assertions about finite classical alphabets and arbitrary finite-dimensional quantum auxiliaries; every law and conditional density is normalized, and information is measured in bits.
--
--   1. For every finite collection $X_1,\ldots,X_m$, the quantum entropy hull $\operatorname{QConvHull}(G)$ equals the finite classical entropy hull $\operatorname{ConvHull}(G)$. A hull point retains both the joint source law and all the coordinates $H(X_i\mid F)$ or $H(X_i\mid C)$.
--   2. For every cq channel $x\mapsto\rho_x^F$ and every $\epsilon>0$, there is a finite classical channel $X\to C$, fixed independently of the input law, such that $|I(X;F)-I(X;C)|\le\epsilon$ for every probability law on $X$.
--   3. For every finite law $q(x,y,z)$, there is a finite classical channel $X\to C_*$ attaining the maximum of $I(F;Y)-I(F;Z)$ among all finite quantum channels $X\to F$. The resulting extensions obey $F-X-YZ$ and $C_*-X-YZ$.
--
--   Writing these propositions as $A_1,A_2,A_3$, one has
--
--   $$
--   (A_1\Longleftrightarrow A_2)\quad\text{and}\quad(A_2\Longleftrightarrow A_3).
--   $$
--
--   This equivalence links quantum entropy convexification, uniform channel-curve approximation, and attained classical optimization. The optimizer clause is an attainment claim, not just equality of two suprema.
-- source:
--   On Dimension Bounds for Auxiliary Quantum Systems, arXiv:1207.3911v4, PDF p. 10, Theorem 3(a): three equivalent universal assertions

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P47

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P47

open QAlgorithms.Papers.Independent.Information100.P27 (shannon average)

open QAlgorithms.Papers.Independent.Information100.P39 (pushLaw)

open QAlgorithms.Papers.Independent.Information100.P48 (normalize)

open QAlgorithms.Papers.Independent.Information100.P62 (IsProjection)

/-- Theorem 3(a), PDF p.10. Absolute-value bars verified in the rendered PDF. -/
theorem three_assertions_equivalent :
    (AssertionOne ↔ AssertionTwo) ∧ (AssertionTwo ↔ AssertionThree) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P47

end
