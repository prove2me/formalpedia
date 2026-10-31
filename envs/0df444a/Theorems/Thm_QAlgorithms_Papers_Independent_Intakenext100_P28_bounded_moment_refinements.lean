-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_bounded_moment_refinements
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.bounded_moment_refinements
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:39:13.169475+00:00
-- url     : https://prove2.me/theorems/90fe4b4b-92c0-4845-9e14-79fc4ebc5707
-- title:
--   Theorem 24: For beta1,beta2 in (0,1), c<= (beta1^{-1}-1)(1-beta2), attainable on a binary alphabet; D is bounded by the minimum of all three expressions (312)–(314)
-- statement:
--   With $0<\beta_1,\beta_2<1$, let $c=\chi^2(P\|Q)$ and $x=(\beta_1^{-1}-1)/(\beta_1^{-1}\beta_2^{-1}-1)$. Then
--
--   $$c\le(\beta_1^{-1}-1)(1-\beta_2),$$
--
--   and $D(P\|Q)$ is at most the minimum of
--
--   $$\log_b(1+c)-\frac{3c\log_b e/2}{1+(1+\beta_2^{-1})(1+c)},\quad
--   \frac{[\sqrt{c^2+8\beta_2c\ln(1+c)}-c]\log_b e}{4\beta_2},\quad
--   d(x\|\beta_2^{-1}x).$$
--
--   Here $d$ is binary relative entropy in base $b$. The first bound is attained by the binary pair $P(0)=x$, $Q(0)=\beta_2^{-1}x$ with exactly the prescribed betas. All density-bounded divergences in these formulas are finite.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 43, Theorem 24

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Theorem 24: For beta1,beta2 in (0,1), c<= (beta1^{-1}-1)(1-beta2), attainable on a binary alphabet; D is bounded by the minimum of all three expressions (312)–(314). Sason--Verdu, arXiv:1508.00335v7, PDF p.43.  -/
theorem bounded_moment_refinements
    (b : LogBase) {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPQ : P ≪ Q)
    (hb1 : 0 < inverseUpperDensity P Q ∧ inverseUpperDensity P Q < 1) (hb2 : 0 < inverseUpperDensity Q P ∧ inverseUpperDensity Q P < 1) :
    chiSquareDiv P Q ≤ ENNReal.ofReal (((inverseUpperDensity P Q)⁻¹ - 1) * (1 - inverseUpperDensity Q P)) ∧
    (let c := (chiSquareDiv P Q).toReal
     let b1 := inverseUpperDensity P Q
     let b2 := inverseUpperDensity Q P
     let x := (b1⁻¹ - 1) / (b1⁻¹ * b2⁻¹ - 1)
     (kl b P Q).toReal ≤ min
       (logB b (1 + c) - ((3 / 2 : ℝ) * c * logBaseE b) / (1 + (1 + b2⁻¹) * (1 + c)))
       (min ((Real.sqrt (c ^ 2 + 8 * b2 * c * Real.log (1 + c)) - c) * logBaseE b / (4 * b2))
         (binaryKL b x (b2⁻¹ * x)))) ∧
    (∀ b1 b2 : ℝ, 0 < b1 → b1 < 1 → 0 < b2 → b2 < 1 →
      let x := (b1⁻¹ - 1) / (b1⁻¹ * b2⁻¹ - 1)
      let P0 := binary x
      let Q0 := binary (b2⁻¹ * x)
      IsProbabilityMeasure P0 ∧ IsProbabilityMeasure Q0 ∧
      inverseUpperDensity P0 Q0 = b1 ∧ inverseUpperDensity Q0 P0 = b2 ∧
      chiSquareDiv P0 Q0 = ENNReal.ofReal ((b1⁻¹ - 1) * (1 - b2))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
