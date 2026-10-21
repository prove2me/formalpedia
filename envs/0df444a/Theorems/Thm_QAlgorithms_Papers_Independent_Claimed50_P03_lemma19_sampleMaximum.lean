-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P03_lemma19_sampleMaximum
-- name    : QAlgorithms.Papers.Independent.Claimed50.P03.lemma19_sampleMaximum
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:02:02.355929+00:00
-- url     : https://prove2.me/theorems/2dad6ac1-04b9-4486-95ca-53349372b03b
-- title:
--   Lemma 19 (Sample maximum)
-- statement:
--   Let $\mu$ be any Borel probability law on $\mathbb R$, with no moment assumptions. For $0<\epsilon,\delta<1$, take $N=\lceil\log(1/\delta)/\epsilon\rceil$ independent samples $X_1,\ldots,X_N\sim\mu$ and let $\widehat\Theta=\max_iX_i$. Then
--   $$\Pr_{X_1,\ldots,X_N}\{\mu(({-}\infty,\widehat\Theta])\ge1-\epsilon\}\ge1-\delta.$$
--   The outer probability concerns the training sample, while the inner measure concerns a fresh draw. The assumptions force $N\ge1$.
-- source:
--   Learning to predict arbitrary quantum processes, arXiv:2210.14894v3, PDF p. 42, Lemma 19 (Sample maximum)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace

/-- Lemma 19, paper p.42, D56: independent training maximum and fresh-draw
coverage. No moment or integrability assumption on the real random variable. -/
theorem lemma19_sampleMaximum (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (eps delta : ℝ) (he0 : 0 < eps) (he1 : eps < 1)
    (hd0 : 0 < delta) (hd1 : delta < 1) :
    let N := ⌈Real.log (1 / delta) / eps⌉₊
    ENNReal.ofReal (1 - delta) ≤
      (Measure.pi (fun _ : Fin N => mu))
        {x | ENNReal.ofReal (1 - eps) ≤ mu (Set.Iic (sampleMaximum x))} := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P03

end
