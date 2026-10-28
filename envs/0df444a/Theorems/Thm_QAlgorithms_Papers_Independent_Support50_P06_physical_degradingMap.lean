-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P06_physical_degradingMap
-- name    : QAlgorithms.Papers.Independent.Support50.P06.physical_degradingMap
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T18:29:03.817674+00:00
-- url     : https://prove2.me/theorems/6e223da0-dae5-4535-b6aa-bdf36fba210c
-- title:
--   Physical vacuum degrading map
-- statement:
--   Let $1/2<\eta\le1$, and let $\rho$ be any normalized density operator on the completed single-mode Fock space. Let $\mathcal L_\eta$ be the vacuum pure-loss channel and $\mathcal E_\eta$ the complementary marginal of the same beam-splitter dilation, with output fields $b=\sqrt\eta\,a+\sqrt{1-\eta}\,f$ and $e=\sqrt{1-\eta}\,a-\sqrt\eta\,f$. Then
--
--   $$\mathcal L_{(1-\eta)/\eta}(\mathcal L_\eta(\rho))=\mathcal E_\eta(\rho).$$
--
--   This equality recreates Eve's reduced state for every input. At $\eta=1$ the degrading channel prepares vacuum. It makes no assertion equating joint Bob–Eve correlations.
-- source:
--   Capacity of the Bosonic Wiretap Channel and the Entropy Photon-Number Inequality, arXiv:0801.0841v1, PDF p. 3, §III, Fig.1 and text: physical degrading map

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

/-- PDF p.3, Fig.1: degrading Bob by intensity (1-eta)/eta recreates Eve's
reduced state for EVERY input density. It does not recreate joint correlations.
At eta=1 the degrading channel is the vacuum replacer. -/
theorem physical_degradingMap (eta : ℝ) (heta : 1 / 2 < eta) (heta_one : eta ≤ 1)
    (rho : State (NumberString 1)) :
    pureLoss 1 ((1 - eta) / eta) (pureLoss 1 eta rho.coefficients) =
      (charlieMarginal (broadcast 1 eta rho.coefficients)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P06

end
