-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P19_appendix_parameters
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P19.appendix_parameters
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:49:58.14519+00:00
-- url     : https://prove2.me/theorems/114e28cf-4633-456a-a2ba-74578b31cdaf
-- title:
--   Appendix A: explicit parameters for dually non-entangling conversion
-- statement:
--   Let $k,d\ge2$ be integers and set $\delta=d^{-4}$ and $\epsilon=d^{-12}$. Then $0<\delta,\epsilon<1$, and both inequalities hold:
--
--   $$1-\delta\le\frac1{1+\frac{d^2}{\sqrt{d-1}}\sqrt{(1-\epsilon)\epsilon}},\qquad d^2(1-\epsilon)\le1+\frac{\sqrt{k-1}}{\sqrt{(1-\delta)\delta}}.$$
--
--   These are the explicit constructed parameter values in Theorem 9.
-- source:
--   Entanglement manipulation and distillability beyond LOCC, arXiv:1711.03835v2, PDF p. 12, appendix-a-parameters

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P19

noncomputable section

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexOrder ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakethird100.P19

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P19 (Bip)

open QAlgorithms.Papers.Independent.Information100.P69 (CP)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P19 (epr)

/-- Appendix A, PDF pp.33-34 (parameters used on p.12): the constructed
values delta=d^(-4), epsilon=d^(-12) satisfy both (10) and (11). -/
theorem appendix_parameters (k d : ℕ) (hk : 2 ≤ k) (hd : 2 ≤ d) :
    let delta := ((d : ℝ) ^ 4)⁻¹
    let epsilon := ((d : ℝ) ^ 12)⁻¹
    0 < delta ∧ delta < 1 ∧ 0 < epsilon ∧ epsilon < 1 ∧
      1 - delta ≤ 1 / (1 + (d : ℝ) ^ 2 / Real.sqrt ((d : ℝ) - 1) *
        Real.sqrt ((1 - epsilon) * epsilon)) ∧
      (d : ℝ) ^ 2 * (1 - epsilon) ≤
        1 + Real.sqrt ((k : ℝ) - 1) / Real.sqrt ((1 - delta) * delta) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P19

end
