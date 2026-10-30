-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P16_preAmplification
-- name    : QAlgorithms.Papers.Independent.Bridge50.P16.preAmplification
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:38:30.124212+00:00
-- url     : https://prove2.me/theorems/60f7ca2f-79b7-46c6-9fee-339747363dab
-- title:
--   Lemma 6, Eqs.(12)–(13): pre-amplification causes less noise
-- statement:
--   For $0<\eta\le1$ and environmental thermal mean $b\ge0$, let $\mathcal N[\eta,b]$, $\mathcal A[G]$ and $\mathcal B_s$ denote the full Fock thermal-loss, quantum-limited amplifier and Gaussian displacement channels. Then
--
--   $$\mathcal N[\eta,b]\circ\mathcal A[1/\eta]=\mathcal B_{(1-\eta)(b+1)}.$$
--
--   The variance $(1-\eta)(b+1)$ is at most $(1-\eta)(b+1)/\eta$, and is strictly smaller when $\eta<1$. Both variances are zero at $\eta=1$. The identity and comparison are conclusions; they explain the advantage of pre-amplification.
-- source:
--   Improved quantum capacity bounds of Gaussian loss channels and achievable rates with Gottesman-Kitaev-Preskill codes, arXiv:1801.07271v2, PDF p. 3, Lemma 6, Eqs.(12)–(13): pre-amplification causes less noise

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P16

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal NNReal Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P16

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Frontier30.P08 (interleavedSymplecticForm)

open QAlgorithms.Papers.Independent.Dependency50.P30 (thermalEntropyBits)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Dependency50.P32 (CPTP applyChoi)

/-- Lemma 6, PDF p.3 Eqs.(12)--(13): both channel identity and noise comparison.
Strict comparison has 0<eta<1; at eta=1 both variances vanish. -/
theorem preAmplification (eta b : ℝ) (h0 : 0 < eta) (h1 : eta ≤ 1) (hb : 0 ≤ b) :
    C.IsNormalFockChannel (C.thermal eta b) ∧
    C.IsNormalFockChannel (C.amplifier (1 / eta)) ∧
    C.IsNormalFockChannel (C.displacementNoiseChannel ((1 - eta) * (b + 1))) ∧
    B.AmplifierRealized (Real.sqrt (1 / eta)) ∧ B.DisplacementRealized ∧
    (∀ X, B.IsTraceClass X → C.thermal eta b (C.amplifier (1 / eta) X) =
      C.displacementNoiseChannel ((1 - eta) * (b + 1)) X) ∧
    (1 - eta) * (b + 1) ≤ (1 - eta) / eta * (b + 1) ∧
    (eta < 1 → (1 - eta) * (b + 1) < (1 - eta) / eta * (b + 1)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P16

end
