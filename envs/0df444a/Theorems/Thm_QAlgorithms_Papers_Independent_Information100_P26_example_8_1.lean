-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_example_8_1
-- name    : QAlgorithms.Papers.Independent.Information100.P26.example_8_1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:01:17.97889+00:00
-- url     : https://prove2.me/theorems/c1341d40-5da7-4153-86c6-dc080fa03579
-- title:
--   Example 8.1: six exact parameter intervals and the transposed EB/MTD cases
-- statement:
--   Let $d\ge2$ and $\lambda\in\mathbb R$, without initially assuming complete positivity, and put $\tau_\lambda=\lambda\operatorname{id}+(1-\lambda)\delta_d$. The exact parameter characterizations are
--   $$\begin{aligned}\tau_\lambda\text{ 2-positive}&\iff -1/(2d-1)\le\lambda\le1,\\tau_\lambda\text{ 2-copositive}&\iff -1/(d-1)\le\lambda\le1/(d+1),\\tau_\lambda\text{ CP}&\iff -1/(d^2-1)\le\lambda\le1,\\tau_\lambda\text{ coCP}&\iff -1/(d-1)\le\lambda\le1/(d+1),\\tau_\lambda\text{ EB}&\iff -1/(d^2-1)\le\lambda\le1/(d+1),\\tau_\lambda\text{ MTD}&\iff -1/(d^2-1)\le\lambda\le1/(d+1).\end{aligned}$$
--   The EB and MTD equivalences also hold separately for $\tau_\lambda\circ T$. All endpoints are included. These intervals supply explicit examples separating the positivity classes; the CP/coCP/EB facts are credited to background references in the source.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 29, Example 8.1

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Example 8.1, PDF pp.29,30. -/
theorem example_8_1 {d : ℕ} (hd : 2 ≤ d) (a : ℝ) :
    let t := depolarizingMixture d a
    (KPositive 2 t ↔ -(1 / (2*(d : ℝ)-1)) ≤ a ∧ a ≤ 1) ∧
    (TwoCopositive t ↔ -(1 / ((d : ℝ)-1)) ≤ a ∧ a ≤ 1 / ((d : ℝ)+1)) ∧
    (CP t ↔ -(1 / ((d : ℝ)^2-1)) ≤ a ∧ a ≤ 1) ∧
    (CoCP t ↔ -(1 / ((d : ℝ)-1)) ≤ a ∧ a ≤ 1 / ((d : ℝ)+1)) ∧
    (EB t ↔ -(1 / ((d : ℝ)^2-1)) ≤ a ∧ a ≤ 1 / ((d : ℝ)+1)) ∧
    (EB (t * transposition d) ↔ -(1 / ((d : ℝ)^2-1)) ≤ a ∧ a ≤ 1 / ((d : ℝ)+1)) ∧
    (MTD t ↔ -(1 / ((d : ℝ)^2-1)) ≤ a ∧ a ≤ 1 / ((d : ℝ)+1)) ∧
    (MTD (t * transposition d) ↔ -(1 / ((d : ℝ)^2-1)) ≤ a ∧ a ≤ 1 / ((d : ℝ)+1)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
