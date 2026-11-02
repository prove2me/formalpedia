-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P19_powerQuotient_bound
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P19.powerQuotient_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:45:35.798546+00:00
-- url     : https://prove2.me/theorems/95976b9c-acda-4778-bb15-25644da61d15
-- title:
--   Lemma 23: scalar power quotient estimate
-- statement:
--   For positive real numbers $x\ne y$ and $r\in(-1,0)\cup(0,1)$,
--
--   $$\frac1r\frac{x^r-y^r}{x-y}\le(\sqrt{xy})^{r-1}.$$
--
--   This is a bound on a scalar divided difference of a real power.
-- source:
--   Entanglement manipulation and distillability beyond LOCC, arXiv:1711.03835v2, PDF p. 29, Lemma 23

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

/-- Lemma 23, PDF p.29: scalar quotient bound; every denominator is guarded. -/
theorem powerQuotient_bound (x y r : ℝ) (hx : 0 < x) (hy : 0 < y) (hne : x ≠ y)
    (hr : (-1 < r ∧ r < 0) ∨ (0 < r ∧ r < 1)) :
    (1 / r) * ((Real.rpow x r - Real.rpow y r) / (x - y)) ≤
      Real.rpow (Real.sqrt (x * y)) (r - 1) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P19

end
