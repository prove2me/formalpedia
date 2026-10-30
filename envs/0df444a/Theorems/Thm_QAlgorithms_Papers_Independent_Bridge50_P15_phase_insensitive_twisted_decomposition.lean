-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P15_phase_insensitive_twisted_decomposition
-- name    : QAlgorithms.Papers.Independent.Bridge50.P15.phase_insensitive_twisted_decomposition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:33:52.208256+00:00
-- url     : https://prove2.me/theorems/666f42fe-a808-4839-b48d-53e836be8241
-- title:
--   Lemma 2: twisted decomposition of every non-EB phase-insensitive Gaussian channel, (49),(50)
-- statement:
--   Let $\mathcal G_{\tau,y}$ be a full-Fock phase-insensitive Gaussian CPTP channel with $\tau\ge0$ and $|1-\tau|\le y<1+\tau$. Its defining Weyl action holds on every normalized input state and has vacuum-$I_2$ noise normalization. Set $\eta'=(1+\tau-y)/2$ and $\kappa'=\tau/\eta'$. Then $0<\eta'\le1$ and $\kappa'\ge1$, the two factors have the corresponding exact Weyl actions, and on every trace-class operator,
--
--   $$\mathcal G_{\tau,y}=\mathcal E_{\eta',0}\circ\mathcal A_{\kappa',0}=\mathcal G_{\eta',1-\eta'}\circ\mathcal G_{\kappa',\kappa'-1}.$$
--
--   The amplifier acts first. This includes attenuators, amplifiers, additive Gaussian noise at $\tau=1$, and identity/quantum-limited boundary cases. At $\tau=0$ the complete-positivity and non-entanglement-breaking noise conditions are incompatible. This generalizes the thermal twisted decomposition without reducing equality to Gaussian-input covariance data.
-- source:
--   Narrow Bounds for the Quantum Capacity of Thermal Attenuators, arXiv:1801.04731v5, PDF p. 10, Lemma 2: twisted decomposition of every non-EB phase-insensitive Gaussian channel, (49),(50)

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

/-- PDF pp.9-10, Lemma 2, (47)-(50): every non-EB phase-insensitive Gaussian
channel, including amplifiers, additive noise, identity and quantum-limited edges.
The all-input Weyl predicate fixes the channel; equality is on all trace class. -/
theorem phase_insensitive_twisted_decomposition (G : Operation ℕ ℕ) (tau y : ℝ)
    (htau : 0 ≤ tau) (hG : PhaseInsensitive G tau y) (hnoise : y < 1 + tau) :
    let etaPrime := (1 + tau - y) / 2
    let kappaPrime := tau / etaPrime
    0 < tau ∧ 0 < etaPrime ∧ etaPrime ≤ 1 ∧ 1 ≤ kappaPrime ∧
    PhaseInsensitive (bosonicChannel etaPrime 0) etaPrime (1 - etaPrime) ∧
    PhaseInsensitive (vacuumChannel (Real.sqrt kappaPrime)) kappaPrime (kappaPrime - 1) ∧
    (∀ X : Matrix ℕ ℕ ℂ, IsTraceClass X →
      G X = bosonicChannel etaPrime 0 (vacuumChannel (Real.sqrt kappaPrime) X)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P15

end
