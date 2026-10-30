-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P16_dataProcessingBound
-- name    : QAlgorithms.Papers.Independent.Bridge50.P16.dataProcessingBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:43:04.314037+00:00
-- url     : https://prove2.me/theorems/019c4568-1a31-4637-a544-045e7c4bf079
-- title:
--   Eq.(29): earlier energy-constrained data-processing bound, rederived
-- statement:
--   For $0\le\eta\le1$, $b\ge0$ and finite input-energy budget $E\ge0$, set $u=\eta/(1+(1-\eta)b)$. The mean-code-state energy-constrained quantum capacity satisfies
--
--   $$Q_E(\mathcal N[\eta,b])\le Q_E(\mathcal N[u,0])=\max\{g(uE)-g((1-u)E),0\}.$$
--
--   The function $g(x)=(1+x)\log_2(1+x)-x\log_2x$ is thermal entropy in bits. The budget applies to the actual encoded maximally mixed state per mode. This is the earlier loss-then-amplifier data-processing bound, rederived in the source.
-- source:
--   Improved quantum capacity bounds of Gaussian loss channels and achievable rates with Gottesman-Kitaev-Preskill codes, arXiv:1801.07271v2, PDF p. 6, Eq.(29): earlier energy-constrained data-processing bound, rederived

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

/-- PDF p.6 Eq.(29), earlier bound [18] Theorems 19 and 24; the code's
input mean energy is unchanged by moving the amplifier to the decoder. -/
theorem dataProcessingBound (eta b budget : ℝ)
    (h0 : 0 ≤ eta) (h1 : eta ≤ 1) (hb : 0 ≤ b) (hbudget : 0 ≤ budget) :
    energyCapacity (coefficientChannel (C.thermal eta b)) budget ≤
      energyCapacity (coefficientChannel (C.thermal (eta / (1 + (1 - eta) * b)) 0)) budget ∧
    energyCapacity (coefficientChannel (C.thermal (eta / (1 + (1 - eta) * b)) 0)) budget =
      ENNReal.ofReal (max (thermalEntropyBits ((eta / (1 + (1 - eta) * b)) * budget) -
        thermalEntropyBits ((1 - eta / (1 + (1 - eta) * b)) * budget)) 0) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P16

end
