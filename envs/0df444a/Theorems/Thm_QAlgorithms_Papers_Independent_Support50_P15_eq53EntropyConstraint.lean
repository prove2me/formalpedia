-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P15_eq53EntropyConstraint
-- name    : QAlgorithms.Papers.Independent.Support50.P15.eq53EntropyConstraint
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:50:04.401384+00:00
-- url     : https://prove2.me/theorems/eadc8438-de6b-4dab-a45a-afd3272b9379
-- title:
--   eq53 entropy constraint
-- statement:
--   Let $d\ge2$, $\rho$ be a normalized density matrix, and $S(\rho)<R\le\log d$. Let $E=\{\sigma:S(\sigma)>R\}$ range over normalized states in the same dimension, and take the infimum in the extended real order. Then
--
--   $$\operatorname{dist}(E,\rho):=\inf_{\sigma\in E}D(\sigma\|\rho)\ge M(R-S(\rho),d).$$
--
--   At $R=\log d$ the strict constraint set is empty and its distance is $+\infty$. The statement includes classical laws as diagonal matrices and does not assert the cited source-coding error-exponent identification. It gives the entropy-constraint consequence of the sharp divergence bound.
-- source:
--   Tight bound on relative entropy by entropy difference, arXiv:1304.0036v3, PDF p. 16, eq53-entropy-constraint

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P15

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Matrix ComplexConjugate ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Support50.P15

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

/-- Entropy-constraint application following (53), PDF p.16, including the empty endpoint. -/
theorem eq53EntropyConstraint {d : ℕ} (hd : 2 ≤ d) (a : EntropyState d) (r : ℝ)
    (hr : entropy a.val < r) (hrd : r ≤ Real.log d) :
    tightBound d (r - entropy a.val) ≤ entropyConstraintDistance r a ∧
    (r = Real.log d → entropyConstraintDistance r a = ⊤) := by sorry

end QAlgorithms.Papers.Independent.Support50.P15

end
