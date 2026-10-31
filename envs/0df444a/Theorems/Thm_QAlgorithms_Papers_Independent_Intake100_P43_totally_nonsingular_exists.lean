-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P43_totally_nonsingular_exists
-- name    : QAlgorithms.Papers.Independent.Intake100.P43.totally_nonsingular_exists
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:28:00.778981+00:00
-- url     : https://prove2.me/theorems/2e5d9172-d22b-4d21-a856-784458166061
-- title:
--   Lemma 8: totally nonsingular matrices exist
-- statement:
--   For every integer $n\ge0$, there is a complex $n\times n$ matrix $M$ for which every square minor is nonzero:
--
--   $$\det M_{R,C}\ne0\qquad (|R|=|C|).$$
--
--   The row and column selections contain distinct indices. The order-zero determinant is one, so the statement includes $n=0$. Such matrices supply the column combinations used in the attaining construction.
-- source:
--   On the dimension of subspaces with bounded Schmidt rank, arXiv:0706.0705v1, PDF p. 2, Lemma 8

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P43

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intake100.P43

open QAlgorithms.Papers.Independent.Dependency50.P50 (Bipartite schmidtNumber)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

/-- PDF p.2, Lemma 8: square totally nonsingular complex matrices exist in
every dimension, including zero (empty determinant one). -/
theorem totally_nonsingular_exists (n : ℕ) :
    ∃ M : Matrix (Fin n) (Fin n) ℂ, TotallyNonsingular M := by sorry

end QAlgorithms.Papers.Independent.Intake100.P43

end
