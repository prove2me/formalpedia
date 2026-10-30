-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P16_lossThenAmplifier
-- name    : QAlgorithms.Papers.Independent.Bridge50.P16.lossThenAmplifier
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:39:24.403307+00:00
-- url     : https://prove2.me/theorems/d1c5db45-add6-4e58-b4a0-9e8bd189a057
-- title:
--   Lemma 7, Eq.(15): loss followed by amplification decomposition
-- statement:
--   Let $0\le\eta\le1$ and $b\ge0$, and set $G=1+(1-\eta)b$ and $\eta'=\eta/G$. Thermal loss decomposes on every trace-class input as
--
--   $$\mathcal N[\eta,b]=\mathcal A[G]\circ\mathcal N[\eta',0].$$
--
--   The gain satisfies $G\ge1$ and the pure-loss transmissivity lies in $[0,1]$, including both physical endpoints. This is the loss-then-amplifier decomposition underlying the earlier data-processing bound.
-- source:
--   Improved quantum capacity bounds of Gaussian loss channels and achievable rates with Gottesman-Kitaev-Preskill codes, arXiv:1801.07271v2, PDF p. 4, Lemma 7, Eq.(15): loss followed by amplification decomposition

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

/-- Lemma 7, PDF p.4 Eq.(15), credited to [18] Eq.(5.1). -/
theorem lossThenAmplifier (eta b : ℝ) (h0 : 0 ≤ eta) (h1 : eta ≤ 1) (hb : 0 ≤ b) :
    C.IsNormalFockChannel (C.thermal eta b) ∧
    C.IsNormalFockChannel (C.amplifier (1 + (1 - eta) * b)) ∧
    C.IsNormalFockChannel (C.thermal (eta / (1 + (1 - eta) * b)) 0) ∧
    B.AmplifierRealized (Real.sqrt (1 + (1 - eta) * b)) ∧
    ∀ X, B.IsTraceClass X → C.thermal eta b X =
      C.amplifier (1 + (1 - eta) * b) (C.thermal (eta / (1 + (1 - eta) * b)) 0 X) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P16

end
