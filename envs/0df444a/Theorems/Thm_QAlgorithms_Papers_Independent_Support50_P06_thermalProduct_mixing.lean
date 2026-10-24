-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P06_thermalProduct_mixing
-- name    : QAlgorithms.Papers.Independent.Support50.P06.thermalProduct_mixing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:34:23.630804+00:00
-- url     : https://prove2.me/theorems/fd691cf5-d34f-45d6-84c7-febea624916e
-- title:
--   Independent thermal products remain thermal under beam splitting
-- statement:
--   Let $n\ge1$, $0\le\eta\le1$, and finite $A,B\ge0$. Feed the independent products $\rho_T(A)^{\otimes n}$ and $\rho_T(B)^{\otimes n}$ to the two ports of the source beam splitter, with retained field $c=\sqrt\eta\,a+\sqrt{1-\eta}\,b$. Then the actual reduced output density and its entropy are
--
--   $$\rho_c=\rho_T(\eta A+(1-\eta)B)^{\otimes n},\qquad S(\rho_c)=n g(\eta A+(1-\eta)B).$$
--
--   This supplies the thermal comparison output used in the EPnI argument. Both transmissivity endpoints and $A=B=0$ are included.
-- source:
--   Capacity of the Bosonic Wiretap Channel and the Entropy Photon-Number Inequality, arXiv:0801.0841v1, PDF p. 4, §V proof and bibliography note [13]: mixing independent thermal products

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P06

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P06

open MeasureTheory Filter

open scoped ENNReal BigOperators Topology

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity rankOne)

open QAlgorithms.Papers.Independent.Next46.P32
  (NumberString FockKernel identicalThermalKernel vacuum productCoherentKernel
   jointMix bobMarginal charlieMarginal pureLoss broadcast mixedOutput
   spectralEntropyNats FockPOVM realFockTracePair modeEnergy complexNormal
   StrongConjecture2)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Claimed50.P11 (thermalEntropyInverse)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.4–5, §V and note [13]: mixing independent identical thermal
products yields the actual identical thermal output, not merely its covariance.
The output mean per mode is eta*A+(1-eta)*B. Both endpoints and A=B=0 remain. -/
theorem thermalProduct_mixing (n : ℕ) (hn : 0 < n) (eta A B : ℝ)
    (heta : 0 ≤ eta) (heta_one : eta ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    mixedOutput n eta (identicalThermalKernel n A) (identicalThermalKernel n B) =
      identicalThermalKernel n (eta * A + (1 - eta) * B) ∧
    spectralEntropyNats
      (mixedOutput n eta (identicalThermalKernel n A) (identicalThermalKernel n B)) =
      ENNReal.ofReal ((n : ℝ) * g (eta * A + (1 - eta) * B)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P06

end
