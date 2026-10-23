-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P23_projectiveQubitEquality
-- name    : QAlgorithms.Papers.Independent.Information100.P23.projectiveQubitEquality
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:11:34.914148+00:00
-- url     : https://prove2.me/theorems/4ce2677f-178c-45cc-b03d-2e61d0d01c84
-- title:
--   §4 unnumbered: projective qubit measure-and-prepare equality family
-- statement:
--   Fix a normalized qubit Bloch basis and unit vectors $m,s_1,s_2\in\mathbb R^3$. Set $\rho(s)=(I+s\cdot\lambda)/2$ and define the two-outcome channel $\Phi(X)=\operatorname{Tr}(\rho(m)X)\rho(s_1)+\operatorname{Tr}(\rho(-m)X)\rho(s_2)$. It is completely positive, trace preserving, and entanglement breaking, with computed data
--
--   $$c=\frac{s_1+s_2}{2},\qquad A=\frac12(s_1-s_2)m^{\mathsf T},\qquad |s_k-c|=\frac12|s_1-s_2|\quad(k=1,2).$$
--
--   The matrix has rank at most one, and has rank one when $s_1\ne s_2$. Moreover,
--
--   $$\|A\|_*^2+|c|^2=\frac14\bigl(|s_1-s_2|^2+|s_1+s_2|^2\bigr)=1.$$
--
--   Here $c\ne0$ exactly when $s_1+s_2\ne0$. This family supplies nonunital sharp examples and includes both identical and antipodal outputs.
--
--   **Formalization Note** The printed claim of rank one is corrected to rank at most one to include the allowed case $s_1=s_2$; the correction requires independent moderation.
-- source:
--   A sharp norm inequality for entanglement-breaking channels, arXiv:2609.27906v1, PDF p. 3, §4 unnumbered: projective qubit measure-and-prepare equality family

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P23

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Information100.P23

/-- PDF p.3, §4, projective qubit equality family.
Source correction: the printed "rank one" is "rank at most one" when s1=s2;
rank is exactly one for distinct outputs. No family member is excluded. -/
theorem projectiveQubitEquality (B : BlochBasis 2) (m s1 s2 : BlochVector 2)
    (hm : vectorNorm m = 1) (hs1 : vectorNorm s1 = 1) (hs2 : vectorNorm s2 = 1) :
    let Phi := projectivePreparation B m s1 s2
    let A := blochA B Phi
    let c := blochC B Phi
    IsCPTP Phi ∧ Entanglement.IsEntanglementBreakingPositive Phi ∧
    c = (1 / 2 : ℝ) • (s1 + s2) ∧
    A = (fun i j => (1 / 2 : ℝ) * (s1 i - s2 i) * m j) ∧
    vectorNorm (s1 - c) = (1 / 2 : ℝ) * vectorNorm (s1 - s2) ∧
    vectorNorm (s2 - c) = (1 / 2 : ℝ) * vectorNorm (s1 - s2) ∧
    A.rank ≤ 1 ∧ (s1 ≠ s2 → A.rank = 1) ∧
    nuclearNorm A ^ 2 + vectorNorm c ^ 2 =
      (1 / 4 : ℝ) * (vectorNorm (s1 - s2) ^ 2 + vectorNorm (s1 + s2) ^ 2) ∧
    nuclearNorm A ^ 2 + vectorNorm c ^ 2 = 1 ∧
    (c ≠ 0 ↔ s1 + s2 ≠ 0) := by sorry

end QAlgorithms.Papers.Independent.Information100.P23

end
