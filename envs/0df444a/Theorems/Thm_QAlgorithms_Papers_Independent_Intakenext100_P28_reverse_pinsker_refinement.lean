-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_reverse_pinsker_refinement
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.reverse_pinsker_refinement
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:50:36.337182+00:00
-- url     : https://prove2.me/theorems/09b351c2-f7c7-4b50-ba2b-6fa1ebc8a5a2
-- title:
--   Remark 28 and Appendix F: improved reverse Pinsker bounds (345)–(350)
-- statement:
--   Let $a=\beta_1^{-1}$, $l=\beta_2$, $V=|P-Q|$, $c=\chi^2(P\|Q)$, and $S=E_Q[Z(Z-1)1_{Z>1}]$, with $0<\beta_1<1$, $\beta_2<1$. Then
--
--   $$D\le\tfrac12[\phi(a)-\phi(l)-a\phi'(a)]V+\phi'(a)S,\qquad
--   c+lV/2\le S\le c+V/2.$$
--
--   The sandwich width is $(1-l)V/2=(1-l)E_Q(1-Z)^+\le(1-l)^2\le1$. Consequently
--
--   $$D\le\tfrac12[\phi(a)-\phi(l)+\phi'(a)(1-a)]V+\phi'(a)c.$$
--
--   These include (345)–(350). Bounded density makes the moments finite; $\phi$ is the continuous function (333).
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 48, Remark 28 and Appendix F

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Remark 28 and Appendix F: improved reverse Pinsker bounds (345)–(350). Sason--Verdu, arXiv:1508.00335v7, PDF p.48.  -/
theorem reverse_pinsker_refinement
    (b : LogBase) {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hb1 : 0 < inverseUpperDensity P Q ∧ inverseUpperDensity P Q < 1) (hb2 : inverseUpperDensity Q P < 1) :
    (let a := (inverseUpperDensity P Q)⁻¹
     let l := inverseUpperDensity Q P
     let v := (fullVariation P Q).toReal
     let c := (chiSquareDiv P Q).toReal
     let s := (truncatedSecond P Q).toReal
     (kl b P Q).toReal ≤ (reversePinskerPhi b a - reversePinskerPhi b l - deriv (reversePinskerPhi b) a * a) * v / 2 + deriv (reversePinskerPhi b) a * s ∧
     c + l * v / 2 ≤ s ∧ s ≤ c + v / 2 ∧
     (1 - l) * v / 2 = (1 - l) * (∫⁻ x, ENNReal.ofReal (max (1 - rnDensityReal P Q x) 0) ∂Q).toReal ∧
     (1 - l) * v / 2 ≤ (1 - l) ^ 2 ∧ (1 - l) ^ 2 ≤ 1 ∧
     (kl b P Q).toReal ≤ (reversePinskerPhi b a - reversePinskerPhi b l + deriv (reversePinskerPhi b) a * (1 - a)) * v / 2 +
       deriv (reversePinskerPhi b) a * c) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
