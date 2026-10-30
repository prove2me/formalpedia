-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P16_improvedEnergyBound
-- name    : QAlgorithms.Papers.Independent.Bridge50.P16.improvedEnergyBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:44:59.405238+00:00
-- url     : https://prove2.me/theorems/6c419725-f071-4a55-9e2c-e55c212da373
-- title:
--   Theorem 11, Eqs.(36)–(37): energy-constrained improved bound
-- statement:
--   Let $0\le\eta\le1$, $b\ge0$, $E\ge0$, $t=\eta-(1-\eta)b>0$ and $G=\eta/t$. For the operational mean-code-state energy constraint,
--
--   $$Q_E(\mathcal N[\eta,b])\le Q_{GE+G-1}(\mathcal N[t,0])=\max\!\left\{g(\eta E+(1-\eta)b)-g\!\left(\frac{(1-\eta)(b+1)(\eta E+(1-\eta)b)}{t}\right),0\right\}.$$
--
--   Here $b$ is environmental photon number, $E$ is encoding photon number per mode, and $g(x)=(1+x)\log_2(1+x)-x\log_2x$. The transformed budget accounts for photons added by pre-amplification. This is the constrained improved data-processing bound.
-- source:
--   Improved quantum capacity bounds of Gaussian loss channels and achievable rates with Gottesman-Kitaev-Preskill codes, arXiv:1801.07271v2, PDF p. 6, Theorem 11, Eqs.(36)–(37): energy-constrained improved bound

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

/-- Theorem 11, PDF pp.6--7 Eqs.(36)--(37); independent [18] Theorem 45.
The second g term has b+1, not budget+1. Energy refers to the encoded state. -/
theorem improvedEnergyBound (eta b budget : ℝ) (h0 : 0 ≤ eta) (h1 : eta ≤ 1)
    (hb : 0 ≤ b) (hbudget : 0 ≤ budget) (ht : 0 < eta - (1 - eta) * b) :
    energyCapacity (coefficientChannel (C.thermal eta b)) budget ≤
      energyCapacity (coefficientChannel (C.thermal (eta - (1 - eta) * b) 0))
        (eta / (eta - (1 - eta) * b) * budget + (eta / (eta - (1 - eta) * b) - 1)) ∧
    energyCapacity (coefficientChannel (C.thermal (eta - (1 - eta) * b) 0))
        (eta / (eta - (1 - eta) * b) * budget + (eta / (eta - (1 - eta) * b) - 1)) =
      ENNReal.ofReal (max (thermalEntropyBits (eta * budget + (1 - eta) * b) -
        thermalEntropyBits ((1 - eta) * (b + 1) * (eta * budget + (1 - eta) * b) /
          (eta - (1 - eta) * b))) 0) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P16

end
