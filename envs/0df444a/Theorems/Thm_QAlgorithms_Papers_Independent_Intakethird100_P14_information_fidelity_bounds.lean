-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P14_information_fidelity_bounds
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P14.information_fidelity_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:54:05.364908+00:00
-- url     : https://prove2.me/theorems/4df1d994-06b2-4704-865d-093926bd2662
-- title:
--   Symmetric Holevo information versus squared fidelity
-- statement:
--   Let $W:b\mapsto\rho_b$, $b\in\{0,1\}$, be a classical–quantum channel whose outputs are positive trace-one density operators on a common complex Hilbert space. Define $F(W)=\|\sqrt{\rho_0}\sqrt{\rho_1}\|_1^2$ and let $I(W)$ be the Holevo information of the uniform input distribution, measured in bits. Then
--
--   $$\log_2\!\frac{2}{1+\sqrt{F(W)}}\ \le\ I(W)\ \le\ \sqrt{1-F(W)}.$$
--
--   These inequalities connect information and reliability, including identical outputs and orthogonal outputs. For infinite-entropy states, $I(W)$ is intrinsically $\tfrac12[D(\rho_0\|\bar\rho)+D(\rho_1\|\bar\rho)]$, where $\bar\rho=(\rho_0+\rho_1)/2$ and relative entropy uses base-two logarithms. Its extended value is retained until the displayed upper bound ensures finiteness.
-- source:
--   Polar codes for classical-quantum channels, arXiv:1109.2591v3, PDF p. 3, Proposition 1: symmetric Holevo information versus fidelity

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P14

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P14

open Filter MeasureTheory

open scoped ENNReal NNReal ComplexOrder BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

open QAlgorithms.Papers.Independent.Dependency50.P13 (compression)

open QAlgorithms.Papers.Independent.Renew46.P44 (wordOutput)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 1, PDF p.3, (1)–(2); proof p.10. The intrinsic information
remains extended until the upper bound establishes finiteness. All outputs
are normalized positive trace-class operators; no finite entropy hypothesis. -/
theorem information_fidelity_bounds {I : Type} (W : Bit → OutputCoefficients I) (hW : IsBinaryCqChannel W) :
    ENNReal.ofReal (Real.logb 2 (2 / (1 + Real.sqrt (squaredCqFidelity W)))) ≤
      symmetricInformation W ∧
    symmetricInformation W ≤ ENNReal.ofReal (Real.sqrt (1 - squaredCqFidelity W)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P14

end
