-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P19_dividedDifference_bound
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P19.dividedDifference_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:44:49.251898+00:00
-- url     : https://prove2.me/theorems/e15a90fa-1a53-424c-a557-d3027d26a398
-- title:
--   Lemma 22: power divided-difference estimate
-- statement:
--   Let $\alpha\in(0,1)\cup(1,2]$ and $p,q\in(0,1]$. For $f_\alpha(x)=x^{1-\alpha}$ on positive reals, let $f_\alpha^{[1]}(x,y)=(f_\alpha(x)-f_\alpha(y))/(x-y)$ if $x\ne y$ and $f_\alpha^{[1]}(x,x)=(1-\alpha)x^{-\alpha}$. Then
--
--   $$0\le\frac{\sqrt{pq}}{1-\alpha}f_\alpha^{[1]}(p^{1/\alpha},q^{1/\alpha})\le1.$$
--
--   This is the scalar estimate used in the pure-state relative-Renyi formula.
-- source:
--   Entanglement manipulation and distillability beyond LOCC, arXiv:1711.03835v2, PDF p. 28, Lemma 22

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

/-- Lemma 22, PDF pp.28-30: divided-difference bound including p=q and alpha=2. -/
theorem dividedDifference_bound (alpha p q : ℝ)
    (ha : (0 < alpha ∧ alpha < 1) ∨ (1 < alpha ∧ alpha ≤ 2))
    (hp : 0 < p) (hp1 : p ≤ 1) (hq : 0 < q) (hq1 : q ≤ 1) :
    let z := Real.sqrt (p * q) / (1 - alpha) *
      powerDividedDifference alpha (Real.rpow p (1 / alpha)) (Real.rpow q (1 / alpha))
    0 ≤ z ∧ z ≤ 1 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P19

end
