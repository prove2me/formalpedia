-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P15_bosonic_bottleneck
-- name    : QAlgorithms.Papers.Independent.Bridge50.P15.bosonic_bottleneck
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:24:33.434475+00:00
-- url     : https://prove2.me/theorems/aa78447b-9eb6-479c-b880-60fb66c452f4
-- title:
--   Abstract/main bosonic bottleneck bound, Eq. (40)
-- statement:
--   Let $0\le\eta<1$ and $N\ge0$ satisfy $\eta'=\eta-N(1-\eta)>0$. Let $\mathcal E_{\eta,N}$ be the single-mode thermal attenuator on the complete Fock space, with intensity transmissivity $\eta$ and bath mean photon number $N$. Its unassisted memoryless quantum capacity, with no input-energy constraint and measured in qubits per use, satisfies
--
--   $$Q(\mathcal E_{\eta,N})\le \max\!\left\{0,\log_2\frac{\eta-N(1-\eta)}{(1+N)(1-\eta)}\right\}.$$
--
--   This is the amplifier-then-loss bottleneck upper bound. The positive numerator and $\eta<1$ are part of its finite-logarithm domain.
-- source:
--   Narrow Bounds for the Quantum Capacity of Thermal Attenuators, arXiv:1801.04731v5, PDF p. 7, Abstract/main bosonic bottleneck bound, Eq. (40)

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

/-- PDF pp.6-7, (36)-(40): unassisted bosonic bottleneck bound in qubits/use,
with no input-energy constraint. The non-EB and eta<1 guards exclude log defaults. -/
theorem bosonic_bottleneck (eta N : ℝ) (heta : 0 ≤ eta) (heta1 : eta < 1)
    (hN : 0 ≤ N) (hprime : 0 < eta - N * (1 - eta)) :
    traceClassQuantumCapacity (bosonicChannel eta N) ≤ ENNReal.ofReal (twistedBound eta N) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P15

end
