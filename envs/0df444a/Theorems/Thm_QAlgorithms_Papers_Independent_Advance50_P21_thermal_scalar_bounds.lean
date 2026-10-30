-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P21_thermal_scalar_bounds
-- name    : QAlgorithms.Papers.Independent.Advance50.P21.thermal_scalar_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:52:12.691329+00:00
-- url     : https://prove2.me/theorems/acd14ebe-89a1-4f03-b936-271f50827cec
-- title:
--   Unnumbered scalar comparison bounds (3.4)–(3.5)
-- statement:
--   Define $g(x)=(x+1)\log(x+1)-x\log x$ on the occupation branch $x\ge0$, with $0\log0=0$, and let $g^{-1}$ denote its nonnegative inverse. For every $x\ge0$ and $y\ge0$,
--   $$1+\log(x+e^{-1})\le g(x)\le1+\log(x+1/2),$$
--   $$e^{y-1}-1/2\le g^{-1}(y)\le e^{y-1}-e^{-1}.$$
--   These scalar comparisons control the thermal entropy and its inverse and include $x=y=0$.
-- source:
--   Entropy power inequalities for qudits, arXiv:1503.04213v3, PDF p. 6, Unnumbered scalar comparison bounds (3.4)–(3.5)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P21

open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)

open QAlgorithms.Papers.Independent.Dependency50.P16 (simplex orderedSpectrum majorizedBy)

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble)

open QAlgorithms.Papers.Independent.Information100.P49 (thermalEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P11 (thermalEntropyInverse)

/-- PDF p.6, (3.4)–(3.5): scalar comparison on nonnegative occupation and entropy branches. -/
theorem thermal_scalar_bounds :
    (∀ x : ℝ, 0 ≤ x →
      1 + Real.log (x + 1 / Real.exp 1) ≤ thermalEntropy x ∧
      thermalEntropy x ≤ 1 + Real.log (x + 1 / 2)) ∧
    (∀ y : ℝ, 0 ≤ y →
      Real.exp (y - 1) - 1 / 2 ≤ thermalEntropyInverse y ∧
      thermalEntropyInverse y ≤ Real.exp (y - 1) - 1 / Real.exp 1) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P21

end
