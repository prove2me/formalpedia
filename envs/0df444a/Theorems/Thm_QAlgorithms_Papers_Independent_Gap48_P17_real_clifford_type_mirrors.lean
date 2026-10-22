-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P17_real_clifford_type_mirrors
-- name    : QAlgorithms.Papers.Independent.Gap48.P17.real_clifford_type_mirrors
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:01:47.619784+00:00
-- url     : https://prove2.me/theorems/4e59972f-8eea-4722-ab5c-db94d5fc88c7
-- title:
--   Corollary 1.8
-- statement:
--   Let $t_{p,q}$ be the actual even/full Clifford type for a nonzero real space. If $8k\ge p,q$ and the reflected signature is also nonzero, then
--   $$t_{p,q}=t_{8k-q,8k-p}.$$
--   On the periodic signature coordinate, including residue-zero representatives of positive dimension, the second mirror exchanges the two algebra types:
--   $$t(7-s)=(t_1(s),t_0(s))\quad\text{when }t(s)=(t_0(s),t_1(s)).$$
--   The additional nonzero restriction on a literal reflected space distinguishes actual Clifford algebras from periodic residue notation.
-- source:
--   Classification of $N$-(super)-extended Poincaré algebras and bilinear invariants of the spinor representation of $Spin(p,q)$, arXiv:math/9511215v1, PDF p. 15, Corollary 1.8

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P17

namespace QAlgorithms.Papers.Independent.Gap48.P17

open scoped BigOperators Matrix.Norms.Elementwise

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Corollary 1.8, PDF p. 15. Printed: the literal signature reflection is stated
under p,q <= 8k. Changed: both actual spaces must be nonzero. Why: the section
assumes V != 0, and p=q=8k would otherwise compare a split even algebra with
the zero-dimensional even algebra R. The periodic table reflection is unchanged. -/
theorem real_clifford_type_mirrors :
    (∀ p q k : ℕ, 0 < p + q → p ≤ 8 * k → q ≤ 8 * k →
      0 < (8 * k - q) + (8 * k - p) →
      ∀ t, HasRealGradedType p q t ↔ HasRealGradedType (8 * k - q) (8 * k - p) t) ∧
    (∀ s : ℤ, realTypeTable (7 - s) = ((realTypeTable s).2, (realTypeTable s).1)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P17
