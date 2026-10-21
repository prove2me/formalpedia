-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P03_lemma17_smallWeight
-- name    : QAlgorithms.Papers.Independent.Claimed50.P03.lemma17_smallWeight
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:00:32.170728+00:00
-- url     : https://prove2.me/theorems/02f12f6b-d880-4311-82db-b6f130bb9ad1
-- title:
--   Lemma 17 (Filtering small weight factor)
-- statement:
--   Let $\widetilde\epsilon,\eta>0$, $|\alpha|\le\eta$, $\beta\in[0,1]$, and $x=\alpha\beta$. Suppose $|\widehat x-x|<\eta\widetilde\epsilon$ and $|\widehat\beta-\beta|<\widetilde\epsilon$. Define $\widehat\alpha=0$ when $\widehat\beta\le2\widetilde\epsilon$, and $\widehat\alpha=\widehat x/\widehat\beta$ otherwise. Then
--   $$\beta|\widehat\alpha-\alpha|^2\le3\eta^2\widetilde\epsilon.$$
--   The denominator is strictly positive whenever it is used. The bound prevents unstable division at small weights.
-- source:
--   Learning to predict arbitrary quantum processes, arXiv:2210.14894v3, PDF p. 38, Lemma 17 (Filtering small weight factor)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace

/-- Lemma 17, paper p.38, D22: strict estimation errors and a guarded division. -/
theorem lemma17_smallWeight (e eta alpha beta xhat bhat : ℝ)
    (he : 0 < e) (heta : 0 < eta) (ha : |alpha| ≤ eta)
    (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1)
    (hx : |xhat - alpha * beta| < eta * e) (hb : |bhat - beta| < e) :
    beta * |smallWeightFilter e xhat bhat - alpha| ^ 2 ≤ 3 * eta ^ 2 * e := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P03

end
