-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P38_unitaryColumn_iff_cokernel
-- name    : QAlgorithms.Papers.Independent.Renew46.P38.unitaryColumn_iff_cokernel
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:09:42.850679+00:00
-- url     : https://prove2.me/theorems/0526f84a-afa6-4172-bf7a-6d2e4df58316
-- title:
--   Hilbert-space criterion for unitary column completion
-- statement:
--   Let $H$ be any complex Hilbert space, $n\geq1$, and $a_1,\ldots,a_n\in B(H)$ with $\sum_i a_i^*a_i=1$. Regard the column as an isometry $a:H\to H^n$. Its adjoint is the computed row $a^*(\xi_1,\ldots,\xi_n)=\sum_i a_i^*\xi_i$. Then
--   $$\text{$(a_1,\ldots,a_n)$ is a column of a unitary on $H^n$}
--   \quad\Longleftrightarrow\quad \ker a^*\cong_{\mathrm{Hilb}}H^{n-1}.$$
--   Here $H^n$ is the Hilbert direct sum and $\cong_{\mathrm{Hilb}}$ means a complex linear isometry equivalence. This is the displayed Hilbert-dimension criterion $\dim\ker a^*=(n-1)\dim H$, including infinite dimension. At $n=1$ it requires zero cokernel and characterizes when the isometry is already unitary.
-- source:
--   Jensen's Operator Inequality, arXiv:math/0204049v1, PDF p. 5, §3, unnumbered: criterion for completing a unital column to a unitary

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P38

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal

namespace QAlgorithms.Papers.Independent.Renew46.P38

universe u

/-- Hansen--Pedersen, §3, PDF p. 5, unitary completion criterion.
The Hilbert-dimension equality is represented by a linear isometry equivalence,
not by algebraic dimension or natural-valued finrank. -/
theorem unitaryColumn_iff_cokernel (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (n : ℕ) (hn : 1 ≤ n)
    (a : Fin n → Operators H) (ha : columnSquares a = 1) :
    IsUnitaryColumn a ↔
      Nonempty ((ColumnCokernel H a) ≃ₗᵢ[ℂ] HilbertPower H (n - 1)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P38

end
