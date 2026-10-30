-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P15_bosonic_extended_upper
-- name    : QAlgorithms.Papers.Independent.Bridge50.P15.bosonic_extended_upper
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:29:43.572991+00:00
-- url     : https://prove2.me/theorems/1404d462-0f66-49ae-bf81-ea0e2b6a731c
-- title:
--   Closed bosonic extended-channel bound, Eq. (33)
-- statement:
--   Let $1/2\le\eta<1$ and $N\ge0$. For the complete-Fock thermal attenuator $\mathcal E_{\eta,N}$ and its purified-environment extension $\mathcal E^e_{\eta,N}$, with no input-energy restriction,
--
--   $$Q(\mathcal E_{\eta,N})\le Q_1(\mathcal E^e_{\eta,N})=\max\left\{0,\log_2\frac{\eta}{1-\eta}+g(N)\right\},$$
--
--   where $g(N)=(N+1)\log_2(N+1)-N\log_2N$ and $g(0)=0$. Capacities are in qubits per use, and $Q_1$ is the reference coherent-information supremum over finite-input-entropy states. The plus sign before $g(N)$ is essential.
--
--   This evaluates the extension's capacity bound; it does not identify the noisy original channel's capacity. The bosonic identity endpoint $\eta=1$ is excluded from this finite real expression.
-- source:
--   Narrow Bounds for the Quantum Capacity of Thermal Attenuators, arXiv:1801.04731v5, PDF p. 6, Closed bosonic extended-channel bound, Eq. (33)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P15

noncomputable section

open Filter

open scoped BigOperators ENNReal Topology Matrix

namespace QAlgorithms.Papers.Independent.Bridge50.P15

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClass IsTraceClassChannel productCoeff tensorApply rankOne)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation conjugateKernel partialLeft partialRight isometryCoeff WeaklyDegradable GaussianDensity)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedRelativeEntropyNats)

open QAlgorithms.Papers.Independent.Gap48.P26
  (entropyBits PhaseInsensitive weightedPhotonExpectation thermalKernel)

open QAlgorithms.Papers.Independent.Claimed50.P35 (traceClassQuantumCapacity vacuumChannel)

open QAlgorithms.Papers.Independent.Dependency50.P30 (thermalEntropyBits)

open QAlgorithms.Papers.Independent.Support50.P07 (qubitPhaseFlipChannel)

open QAlgorithms.Papers.Independent.Information100.P08 (qubitInput thermalChannel)

/-- PDF pp.5-6, (33): closed extension-capacity bound, including the plus g(N).
eta=1 is excluded because the bosonic identity has unbounded capacity. -/
theorem bosonic_extended_upper (eta N : ℝ) (heta : (1 / 2 : ℝ) ≤ eta)
    (heta1 : eta < 1) (hN : 0 ≤ N) :
    traceClassQuantumCapacity (bosonicChannel eta N) ≤ singleLetter (bosonicExtension eta N) ∧
    singleLetter (bosonicExtension eta N) = ENNReal.ofReal (extendedBound eta N) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P15

end
