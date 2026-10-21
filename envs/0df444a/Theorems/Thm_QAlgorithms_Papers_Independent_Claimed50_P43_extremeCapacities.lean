-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P43_extremeCapacities
-- name    : QAlgorithms.Papers.Independent.Claimed50.P43.extremeCapacities
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:29:56.692435+00:00
-- url     : https://prove2.me/theorems/ae33be70-86c9-45b0-a0c0-d7339e8c2647
-- title:
--   Exact capacities at the maximal depolarizing parameter
-- statement:
--   Let $d\ge2$ and let $\Phi$ be the $d$-dimensional depolarizing channel at $p=d^2/(d^2-1)$. Then, in bits,
--
--   $$C_{\rm ea}(\Phi)=\log_2\frac{d^2}{d^2-1},\qquad C^{(1)}(\Phi)=\frac1{d+1}\log_2\frac d{d+1}+\frac d{d+1}\log_2\frac{d^2}{d^2-1}>0.$$
--
--   The negative first logarithm retains its printed plus sign. Positivity ensures that the capacity-enhancement ratio has a nonzero denominator.
-- source:
--   On entanglement-assisted classical capacity, arXiv:quant-ph/0106075v2, PDF p. 8, §III, unnumbered extreme-noise capacity formulas

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P43

noncomputable section

open scoped Matrix ComplexConjugate

open Filter

namespace QAlgorithms.Papers.Independent.Claimed50.P43

open QAlgorithms.Papers.Independent.Dependency50.P45

attribute [local instance] Classical.propDecidable

/-- PDF p.8: exact maximal-noise capacities. The positive unassisted value guards
the enhancement quotient against Lean's division-by-zero default. -/
theorem extremeCapacities (d : ℕ) (hd : 2 ≤ d) :
    let N := QAlgorithms.QuditFidelity.depolarizingMap d (by omega)
      ((d : ℝ)^2 / ((d : ℝ)^2 - 1))
    regularizedAssistedHolevo N = Real.logb 2 ((d : ℝ)^2 / ((d : ℝ)^2 - 1)) ∧
    holevoCapacity N = (1 / ((d : ℝ) + 1)) * Real.logb 2 ((d : ℝ) / (d + 1)) +
      ((d : ℝ) / (d + 1)) * Real.logb 2 ((d : ℝ)^2 / ((d : ℝ)^2 - 1)) ∧
    0 < holevoCapacity N := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P43

end
