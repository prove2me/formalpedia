-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P38_contractiveColumn_unitaryDilation
-- name    : QAlgorithms.Papers.Independent.Renew46.P38.contractiveColumn_unitaryDilation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:10:35.482897+00:00
-- url     : https://prove2.me/theorems/830f9bf9-6f80-42bb-bb2e-5e6c91be660d
-- title:
--   Unitary dilation of a contractive column
-- statement:
--   Let $H$ be a complex Hilbert space, $n\geq1$, and $a_1,\ldots,a_n\in B(H)$ with $\sum_i a_i^*a_i\leq1$. Define the last entry from the given column by the positive square root
--   $$a_{n+1}=\left(1-\sum_{i=1}^n a_i^*a_i\right)^{1/2}.$$
--   Then $(a_1,\ldots,a_n,a_{n+1})$ is a column of an actual unitary $(n+1)\times(n+1)$ operator block matrix on $H^{n+1}$. If the original column is unital, the computed last entry is $0$.
--
--   This supplies a unitary dilation, not merely the identity for the enlarged sum of squares. The extra coordinate is represented formally by the optional index appended to the original finite index set.
-- source:
--   Jensen's Operator Inequality, arXiv:math/0204049v1, PDF p. 5, §3, unnumbered: unitary dilation of every contractive column

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P38

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal

namespace QAlgorithms.Papers.Independent.Renew46.P38

universe u

/-- Hansen--Pedersen, §3, PDF p. 5, unitary dilation of a contractive column.
The last entry is computed by the positive square root, not supplied as extra data. -/
theorem contractiveColumn_unitaryDilation (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (n : ℕ) (hn : 1 ≤ n)
    (a : Fin n → Operators H) (ha : columnSquares a ≤ 1) :
    IsUnitaryColumn (dilatedColumn a) ∧
      (columnSquares a = 1 → dilatedColumn a none = 0) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P38

end
