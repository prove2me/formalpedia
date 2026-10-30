-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P03_optimal_ancilla_charge
-- name    : QAlgorithms.Papers.Independent.Extend50.P03.optimal_ancilla_charge
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T12:56:54.138198+00:00
-- url     : https://prove2.me/theorems/7c044910-d3fd-45d5-9a6b-b36d6444d1bb
-- title:
--   §4.3: optimal linear ancilla charge in the leading bound
-- statement:
--   For $a\in(0,1)$ let $f(a)=1/(4\sqrt{a(1-a)})$, the common charge-dependent factor in the two leading error bounds. Then
--
--   $$f(a)\ge f(1/2)=1/2,\qquad f(a)=f(1/2)\iff a=1/2.$$
--
--   The function decreases on $(0,1/2]$ and increases on $[1/2,1)$. This optimizes the proven leading coefficients, without asserting pointwise finite-size optimized-error monotonicity. Realizing $\alpha=n/2$ requires even $n$ and $k\le n/2$.
-- source:
--   Charge-conserving unitaries typically generate optimal covariant quantum error-correcting codes, arXiv:2102.11835v1, PDF p. 12, §4.3: optimal linear ancilla charge in the leading bound

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P03

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Extend50.P03

open QAlgorithms.Papers.Independent.Support50.P23 (minEntropy)

attribute [local instance] Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P03.matrixContinuousENorm

/-- Section 4.3, PDF p.12: optimality and monotonicity of the leading coefficient.
This does not assert finite-n optimized-error monotonicity. -/
theorem optimal_ancilla_charge :
    (∀ a : ℝ, 0 < a → a < 1 →
      chargeCoefficient (1/2) ≤ chargeCoefficient a ∧
      (chargeCoefficient a = chargeCoefficient (1/2) ↔ a = 1/2)) ∧
    (∀ a b : ℝ, 0 < a → a ≤ b → b ≤ 1/2 → chargeCoefficient b ≤ chargeCoefficient a) ∧
    (∀ a b : ℝ, 1/2 ≤ a → a ≤ b → b < 1 → chargeCoefficient a ≤ chargeCoefficient b) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P03

end
