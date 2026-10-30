-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P16_displacementCapacityBound
-- name    : QAlgorithms.Papers.Independent.Bridge50.P16.displacementCapacityBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:46:08.404736+00:00
-- url     : https://prove2.me/theorems/3a211cbc-626a-45cd-8a86-e032beca6184
-- title:
--   Eq.(42): improved Gaussian displacement capacity upper bound
-- statement:
--   Let $0<s<1$ be quadrature displacement variance, and let $\mathcal B_s$ be the Gaussian random displacement channel with complex-plane density $e^{-|\alpha|^2/s}/(\pi s)$. Its energy-unconstrained quantum capacity satisfies
--
--   $$Q(\mathcal B_s)\le\max\!\left\{\log_2\frac{1-s}{s},0\right\}.$$
--
--   The units are qubits per mode. This is the improved displacement-channel data-processing bound obtained from pre-amplification.
-- source:
--   Improved quantum capacity bounds of Gaussian loss channels and achievable rates with Gottesman-Kitaev-Preskill codes, arXiv:1801.07271v2, PDF p. 7, Eq.(42): improved Gaussian displacement capacity upper bound

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

/-- PDF p.7 Eq.(42): improved displacement-capacity upper bound, 0<s<1.
The printed adjective strictly is not asserted when both clipped bounds vanish. -/
theorem displacementCapacityBound (s : ℝ) (h0 : 0 < s) (h1 : s < 1) :
    T.operationalTraceClassCapacity (coefficientChannel (C.displacementNoiseChannel s)) ≤
      ENNReal.ofReal (max (Real.logb 2 ((1 - s) / s)) 0) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P16

end
