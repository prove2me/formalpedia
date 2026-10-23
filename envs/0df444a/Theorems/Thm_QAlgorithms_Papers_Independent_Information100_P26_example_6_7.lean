-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_example_6_7
-- name    : QAlgorithms.Papers.Independent.Information100.P26.example_6_7
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:56:57.445987+00:00
-- url     : https://prove2.me/theorems/72646312-e3b5-45fa-a1b1-196281625992
-- title:
--   Example 6.7: a 2-copositive channel which is not PPT
-- statement:
--   For $d>2$ and a real parameter in the half-open interval
--   $$-\frac1{2d-1}\le\lambda<-\frac1{d^2-1},$$
--   the map $\tau(X)=\lambda X^T+(1-\lambda)\delta_d(X)$ is a unital channel which is 2-copositive but not PPT. This separates 2-copositivity from complete copositivity among unital channels.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 23, Example 6.7

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Example 6.7, PDF pp.23. -/
theorem example_6_7 {d : ℕ} (hd : 2 < d) (a : ℝ)
    (hlo : -(1 / (2*(d : ℝ)-1)) ≤ a) (hhi : a < -(1 / ((d : ℝ)^2-1))) :
    let t : Map d := a • transposition d + (1-a) • depolarizing d
    UnitalChannel t ∧ TwoCopositive t ∧ ¬ PPT t := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
