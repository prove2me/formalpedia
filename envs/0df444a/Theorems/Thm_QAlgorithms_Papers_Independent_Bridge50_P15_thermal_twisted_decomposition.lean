-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P15_thermal_twisted_decomposition
-- name    : QAlgorithms.Papers.Independent.Bridge50.P15.thermal_twisted_decomposition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:31:21.705272+00:00
-- url     : https://prove2.me/theorems/641692a1-2034-4a66-8bc3-3f372d897825
-- title:
--   Lemma 1: twisted decomposition of a non-EB thermal attenuator, (36),(37)
-- statement:
--   Let $0\le\eta\le1$ and $N\ge0$ satisfy $\eta'=\eta-N(1-\eta)>0$, the non-entanglement-breaking condition away from the identity endpoint. Set $\kappa'=\eta/\eta'$. Then $0<\eta'\le1$, $\kappa'\ge1$, and the quantum-limited factors are CPTP channels satisfying, on every trace-class input operator,
--
--   $$\mathcal E_{\eta,N}=\mathcal E_{\eta',0}\circ\mathcal A_{\kappa',0},\qquad \eta'=\eta-N(1-\eta),\quad\kappa'=\frac\eta{\eta'}.$$
--
--   The amplifier acts first. All maps act on the complete single-mode Fock space, with vacuum covariance $I_2$ and intensity gain/transmissivity parameters. Identity factors at $N=0$ and $\eta=1$ are included. This is full channel equality, rather than merely a moment calculation on Gaussian states, and supplies the decomposition behind the bottleneck bound.
-- source:
--   Narrow Bounds for the Quantum Capacity of Thermal Attenuators, arXiv:1801.04731v5, PDF p. 6, Lemma 1: twisted decomposition of a non-EB thermal attenuator, (36),(37)

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

/-- PDF pp.6-7, Lemma 1, (36)-(37): amplifier FIRST, then loss, on every
trace-class input. N=0 and eta=1 include identity factors. -/
theorem thermal_twisted_decomposition (eta N : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1)
    (hN : 0 ≤ N) (hprime : 0 < eta - N * (1 - eta)) :
    let etaPrime := eta - N * (1 - eta)
    let kappaPrime := eta / etaPrime
    0 < etaPrime ∧ etaPrime ≤ 1 ∧ 1 ≤ kappaPrime ∧
    IsTraceClassChannel (bosonicChannel etaPrime 0) ∧
    IsTraceClassChannel (vacuumChannel (Real.sqrt kappaPrime)) ∧
    (∀ X : Matrix ℕ ℕ ℂ, IsTraceClass X →
      bosonicChannel eta N X = bosonicChannel etaPrime 0 (vacuumChannel (Real.sqrt kappaPrime) X)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P15

end
