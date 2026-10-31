-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P43_column_combination_few_zeros
-- name    : QAlgorithms.Papers.Independent.Intake100.P43.column_combination_few_zeros
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:28:48.409995+00:00
-- url     : https://prove2.me/theorems/02c3bf22-d969-4452-a6b1-a6effa6fa8b7
-- title:
--   Lemma 9: nontrivial column combinations have few zeros
-- statement:
--   Let $1\le n\le m$, let $M\in M_m(\mathbb C)$ be totally nonsingular, and select $n$ distinct columns using an injection $j\mapsto c_j$. For coefficients $a_1,\ldots,a_n$ that are not all zero, put $v_i=\sum_j a_j M_{i,c_j}$. Then
--
--   $$\#\{i:v_i=0\}\le n-1.$$
--
--   Some individual coefficients may vanish. This corrected nontrivial-combination form is the one required by the source’s proof and construction.
-- source:
--   On the dimension of subspaces with bounded Schmidt rank, arXiv:0706.0705v1, PDF p. 2, Lemma 9 (proof continues on PDF p.3)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P43

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intake100.P43

open QAlgorithms.Papers.Independent.Dependency50.P50 (Bipartite schmidtNumber)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

/-- PDF pp.2–3, Lemma 9, corrected from its proof: printed "any linear
combination" must mean a NONTRIVIAL combination of DISTINCT selected columns.
The all-zero coefficient vector contradicts the literal printed statement.
No requirement that all coefficients be individually nonzero is imposed. -/
theorem column_combination_few_zeros (m n : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m)
    (M : Matrix (Fin m) (Fin m) ℂ) (hM : TotallyNonsingular M)
    (cols : Fin n ↪ Fin m) (c : Fin n → ℂ) (hc : c ≠ 0) :
    (Finset.univ.filter (fun i : Fin m =>
      (∑ j : Fin n, c j * M i (cols j)) = 0)).card ≤ n - 1 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P43

end
