-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P38_canonicalDilation_unitary
-- name    : QAlgorithms.Papers.Independent.Renew46.P38.canonicalDilation_unitary
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:10:56.780736+00:00
-- url     : https://prove2.me/theorems/624f58e7-5872-479e-9d06-ca48c9351d46
-- title:
--   Explicit canonical unitary dilation
-- statement:
--   Let $H$ be a complex Hilbert space, $n\geq1$, and $a=(a_1,\ldots,a_n)$ a unital column, so $\sum_i a_i^*a_i=1$. Regard $a:H\to H^n$ as the associated isometry, and compute $p=1-aa^*$. Then $p$ is an orthogonal projection, and the computed block operator on $H^n\oplus H$,
--   $$U=\begin{pmatrix}p&a\\-a^*&0\end{pmatrix},\qquad
--   p_{ij}=\delta_{ij}1-a_i a_j^*,$$
--   is unitary. Its last column is exactly $(a_1,\ldots,a_n,0)$.
--
--   This is the explicit canonical dilation in (11)–(12), with the block order shown by the matrix. The entry printed with $a_m^*$ in the first row of (12) is read as $a_n^*$, as fixed by $p=1-aa^*$ and (11).
-- source:
--   Jensen's Operator Inequality, arXiv:math/0204049v1, PDF p. 5, §3, unnumbered: explicit canonical dilation (11)–(12)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P38

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal

namespace QAlgorithms.Papers.Independent.Renew46.P38

universe u

/-- Hansen--Pedersen, §3, PDF p. 5, explicit canonical dilation (11)--(12).
Block order is H^n ⊕ H. The first-row a_m* in (12) is corrected to a_n* using
(11) and p=1-aa*. The negative sign in the bottom row is retained. -/
theorem canonicalDilation_unitary (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (n : ℕ) (hn : 1 ≤ n)
    (a : Fin n → Operators H) (ha : columnSquares a = 1) :
    IsStarProjection (columnRangeComplement a) ∧
    IsUnitaryMatrix (columnCanonicalDilation a) ∧
    (∀ i : Fin n, columnCanonicalDilation a (some i) none = a i) ∧
    columnCanonicalDilation a none none = 0 := by sorry

end QAlgorithms.Papers.Independent.Renew46.P38

end
