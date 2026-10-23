-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P38_lemma4_hayashiNagaoka
-- name    : QAlgorithms.Papers.Independent.Gap48.P38.lemma4_hayashiNagaoka
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T05:06:29.448034+00:00
-- url     : https://prove2.me/theorems/ae127b12-f215-4862-b793-00ed1f31dfaf
-- title:
--   Lemma 4: Hayashi–Nagaoka operator inequality
-- statement:
--   On a nonempty finite complex register, let $\Pi,\Lambda$ be operators with $0\le\Pi\le I$ and $\Pi\le\Lambda$ in Loewner order. Define $\Lambda^{-1/2}$ spectrally, sending a positive eigenvalue $\lambda$ to $\lambda^{-1/2}$ and a zero eigenvalue to zero. Then
--
--   $$I-\Lambda^{-1/2}\Pi\Lambda^{-1/2}\le2(I-\Pi)+4(\Lambda-\Pi).$$
--
--   This operator inequality, attributed in the source to Hayashi–Nagaoka [24], remains valid when $\Lambda$ is singular and is used in analyzing the pretty-good measurement.
-- source:
--   Optimal quantum source coding with quantum information at the encoder and decoder, arXiv:0706.2907v2, PDF p. 7, Lemma 4: Hayashi–Nagaoka operator inequality

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P38

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Gap48.P38

/-- Lemma 4 (Hayashi--Nagaoka, attributed to [24]), PDF p.7.
Loewner order is expressed by positivity of RHS minus LHS; Lambda may be singular. -/
theorem lemma4_hayashiNagaoka
    (J : Type) [Fintype J] [DecidableEq J] [Nonempty J]
    (Pi Lambda : Matrix J J ℂ) (hPi : IsEffect Pi)
    (hLambda : (Lambda - Pi).PosSemidef) :
    ((2 : ℂ) • (1 - Pi) + (4 : ℂ) • (Lambda - Pi) -
      (1 - QAlgorithms.Papers.Independent.Next46.P39.inverseSqrt Lambda * Pi * QAlgorithms.Papers.Independent.Next46.P39.inverseSqrt Lambda)).PosSemidef := by sorry

end QAlgorithms.Papers.Independent.Gap48.P38

end
