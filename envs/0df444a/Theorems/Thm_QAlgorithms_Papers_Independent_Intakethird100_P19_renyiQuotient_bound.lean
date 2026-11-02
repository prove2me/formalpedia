-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P19_renyiQuotient_bound
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P19.renyiQuotient_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:46:26.080838+00:00
-- url     : https://prove2.me/theorems/9cfc553a-dbc0-450c-afcd-342fe8907b8b
-- title:
--   Lemma 24: off-diagonal Renyi quotient estimate
-- statement:
--   For $p,q\in(0,1]$ with $p\ne q$, and $\alpha\in(0,1)\cup(1,2)$,
--
--   $$\frac{\sqrt{pq}}{1-\alpha}\frac{p^{(1-\alpha)/\alpha}-q^{(1-\alpha)/\alpha}}{p^{1/\alpha}-q^{1/\alpha}}\le1.$$
--
--   This is the off-diagonal form of the estimate used in Lemma 22.
-- source:
--   Entanglement manipulation and distillability beyond LOCC, arXiv:1711.03835v2, PDF p. 29, Lemma 24

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

/-- Lemma 24, PDF p.29: the off-diagonal quotient, with alpha=2 excluded. -/
theorem renyiQuotient_bound (alpha p q : ℝ)
    (ha : (0 < alpha ∧ alpha < 1) ∨ (1 < alpha ∧ alpha < 2))
    (hp : 0 < p) (hp1 : p ≤ 1) (hq : 0 < q) (hq1 : q ≤ 1) (hne : p ≠ q) :
    Real.sqrt (p * q) / (1 - alpha) *
      ((Real.rpow p ((1 - alpha) / alpha) - Real.rpow q ((1 - alpha) / alpha)) /
        (Real.rpow p (1 / alpha) - Real.rpow q (1 / alpha))) ≤ 1 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P19

end
