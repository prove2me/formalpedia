-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P06_highPhoton_capacityLimit
-- name    : QAlgorithms.Papers.Independent.Support50.P06.highPhoton_capacityLimit
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:31:21.95012+00:00
-- url     : https://prove2.me/theorems/2dd552a2-67ad-4a93-8f48-e8cbea831f9f
-- title:
--   Conditional high-photon privacy and coherent-information limits
-- statement:
--   Assume global minimum output entropy conjecture 2 and the same full-oscillator, vacuum-dilation operational privacy convention and mean-photon budget as in the wiretap theorem. For $0<\eta<1$, let $Q^{(1)}(\eta,N)$ denote the coherent-information supremum over all normalized inputs with mean photons at most $N$. In nats,
--
--   $$\lim_{N\to\infty} C_p(\eta,N)=\lim_{N\to\infty}Q^{(1)}(\eta,N)=\max\{0,\ln\eta-\ln(1-\eta)\}.$$
--
--   At $\eta=1$ both limits are $+\infty$. This retains the conjectural premise of the present paper's derivation. The separately cited unconditional quantum-capacity result is inventoried as a deferral.
-- source:
--   Capacity of the Bosonic Wiretap Channel and the Entropy Photon-Number Inequality, arXiv:0801.0841v1, PDF p. 3, §III, unnumbered high-input-photon-number limit

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

/-- PDF p.3, paragraph after (12): conditional high-photon limit in nats for
both operational privacy capacity and constrained Q^(1). The finite logarithm
formula is restricted to 0<eta<1. The eta=1 limit is infinity, not log(0).
The independently cited unconditional result [10] is inventoried separately. -/
theorem highPhoton_capacityLimit (hmoe : StrongConjecture2) :
    (∀ eta : ℝ, 0 < eta → eta < 1 →
      Tendsto (fun N : ℝ => holevoMessagePrivacyCapacityNats 1 eta N) atTop
        (nhds (ENNReal.ofReal (max 0 (Real.log eta - Real.log (1 - eta))))) ∧
      Tendsto (fun N : ℝ => coherentInformationMaximum 1 eta N) atTop
        (nhds ((max 0 (Real.log eta - Real.log (1 - eta)) : ℝ) : EReal))) ∧
    Tendsto (fun N : ℝ => holevoMessagePrivacyCapacityNats 1 1 N) atTop (nhds ⊤) ∧
    Tendsto (fun N : ℝ => coherentInformationMaximum 1 1 N) atTop (nhds ⊤) := by sorry

end QAlgorithms.Papers.Independent.Support50.P06

end
