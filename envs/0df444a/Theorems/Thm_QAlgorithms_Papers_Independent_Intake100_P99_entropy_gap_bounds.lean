-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P99_entropy_gap_bounds
-- name    : QAlgorithms.Papers.Independent.Intake100.P99.entropy_gap_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:13:40.968823+00:00
-- url     : https://prove2.me/theorems/5730fd2c-1a65-4f3a-8e97-40b5fca26fe8
-- title:
--   Two upper bounds for the entropy-gap branch
-- statement:
--   For $0\leq\Delta\leq\tfrac12$, let $f(\Delta)\in[0,\tfrac12]$ be the unique nonnegative branch satisfying $H_2(\tfrac12-f(\Delta))+H_2(\Delta)=1$, where $H_2$ denotes binary entropy in bits. Then
--
--   $$
--   f(\Delta)^2\leq\frac{\ln2}{2}H_2(\Delta),\qquad
--   f(\Delta)\leq\sqrt{\frac\Delta2\ln\frac e\Delta}.
--   $$
--
--   The second expression is defined as zero at $\Delta=0$, its continuous limiting value. Here $e=\exp(1)$ and $\ln$ is the natural logarithm. These estimates provide explicit disturbance bounds without solving the entropy equation numerically.
--
--   **Formalization Note** The source prose says convexity, although binary entropy is concave; only the two displayed inequalities are asserted.
-- source:
--   Security of quantum key distribution with imperfect devices, arXiv:quant-ph/0212066v3, PDF p. 11, Unnumbered entropy-gap estimates, eqs.(21)–(22)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P99

noncomputable section

open scoped Matrix ComplexConjugate BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P99

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P69 (diamond)

open QAlgorithms.Papers.Independent.Dependency50.P48 (IsDilation receiver)

/-- arXiv:quant-ph/0212066v3, PDF p.11, (21)--(22).
The square root contains the WHOLE product (delta/2) ln(e/delta).
At delta=0 the logarithmic envelope is its continuous extension zero.
The source prose says convexity; binary entropy is concave. Only its displayed
inequalities are asserted here; no convexity claim is imported. -/
theorem entropy_gap_bounds (delta : ℝ) (hdelta : 0 ≤ delta ∧ delta ≤ 1 / 2) :
    entropyGap delta ^ 2 ≤ (1 / 2) * Real.log 2 * binEntropy2 delta ∧
    entropyGap delta ≤
      (if delta = 0 then 0 else Real.sqrt ((delta / 2) * Real.log (Real.exp 1 / delta))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P99

end
