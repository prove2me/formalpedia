-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P09_u1_constantCharge_examples
-- name    : QAlgorithms.Papers.Independent.Extend50.P09.u1_constantCharge_examples
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:42:22.888579+00:00
-- url     : https://prove2.me/theorems/7eb26611-e097-47ce-a6c9-a718c71a7dcd
-- title:
--   Appendix C1: fixed-charge examples k=t=1 and k=t=2
-- statement:
--   Fix a nonnegative integer $\alpha$. For each sufficiently large integer $n$, let $F_{11}(n)$ and $F_{22}(n)$ be the root fidelities between the exact averaged U(1) Choi environment state and its product comparator $I_R/2^k\otimes\zeta_0$, separately for $k=t=1$ and $k=t=2$, with $\zeta_0$ the environmental marginal. Then
--   $$F_{11}(n)=1+\frac{c_{11}}n+O(n^{-2}),\quad
--   c_{11}=\frac{-\sqrt2-2\sqrt2\alpha+\sqrt{\alpha(2\alpha+1)}+\sqrt{(\alpha+1)(2\alpha+1)}}{2\sqrt2},$$
--   $$F_{22}(n)=1+\frac{c_{22}}n+O(n^{-2}),\quad
--   c_{22}=\frac{-2-2\alpha+\sqrt{\alpha(\alpha+1)}+\sqrt{(\alpha+1)(\alpha+2)}}2.$$
--   For the associated purified distances $P_{11},P_{22}$,
--   $$P_{11}(n),P_{22}(n)=O(n^{-1/2}).$$
--
--   The constants may depend on fixed $\alpha$. These are comparator expansions, not exact optimized recovery errors.
-- source:
--   Near-optimal covariant quantum error-correcting codes from random unitaries with symmetries, arXiv:2112.01498v2, PDF p. 20, Appendix C1: fixed-charge examples k=t=1 and k=t=2

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P09

noncomputable section

open scoped Matrix Matrix.Norms.Elementwise ComplexConjugate ENNReal ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Extend50.P09

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact generic definitions from the pinned accepted library.

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed bell)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalMinEntropy)

open QAlgorithms.Papers.Independent.Advance50.P02 (negLog)

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P09.covariantMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P09.covariantMatrixBorel

/-- Appendix C1, PDF p.20, (C17)–(C18): both fixed-charge examples,
including alpha=0. These are comparator distances, not exact recovery errors. -/
theorem u1_constantCharge_examples (alpha : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, ∀ n ≥ n0, alpha+2 ≤ n → 0 < n →
    |comparatorFidelity n 1 1 alpha-(1+constantCoeff11 alpha/n)| ≤ C/(n : ℝ)^2 ∧
    |comparatorFidelity n 2 2 alpha-(1+constantCoeff22 alpha/n)| ≤ C/(n : ℝ)^2 ∧
    comparatorDistance n 1 1 alpha ≤ C/Real.sqrt n ∧
    comparatorDistance n 2 2 alpha ≤ C/Real.sqrt n := by sorry

end QAlgorithms.Papers.Independent.Extend50.P09

end
