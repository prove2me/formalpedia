-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P15_bosonic_thermal_optimization
-- name    : QAlgorithms.Papers.Independent.Bridge50.P15.bosonic_thermal_optimization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:28:47.490653+00:00
-- url     : https://prove2.me/theorems/60d714be-a7a2-4c51-9b73-5a846ffce433
-- title:
--   Thermal optimization and infinite-energy reduction for the bosonic extension, (30)–(32)
-- statement:
--   Let $1/2\le\eta<1$ and $N\ge0$. Let $\mathcal E^e_{\eta,N}$ be the full-Fock extension obtained from the beam splitter (12)–(13) and the actual thermal two-mode Schmidt purification (29). This extension is degradable relative to its computed true complement. Define $J$ in bits through the finite-input-entropy reference definition, and let $Q_1$ be its extended nonnegative optimization supremum. Then
--
--   $$Q(\mathcal E_{\eta,N})\le Q_1(\mathcal E^e_{\eta,N})=\sup_{\rho_G}J(\rho_G,\mathcal E^e_{\eta,N})=\lim_{n\to\infty}J(\tau_n,\mathcal E^e_{\eta,N})<\infty.$$
--
--   Here $\rho_G$ ranges over normalized Gaussian input states and $\tau_n$ is the thermal state of mean photon number $n\ge0$, with covariance $(2n+1)I_2$ in the vacuum-$I_2$ convention. For every finite $n$, the thermal input, extension output, and true complementary output have finite entropy. Every normalized input state $\rho$ of mean photon number exactly $n$ has finite entropy and satisfies
--
--   $$J(\rho,\mathcal E^e_{\eta,N})\le J(\tau_n,\mathcal E^e_{\eta,N})=-J(\tau_n,\bar{\mathcal E}_{\eta,N})=-J(\tau_n,\mathcal E_{1-\eta,N}).$$
--
--   The fixed-energy comparison ranges over all states, including non-Gaussian states. This reduces the unconstrained extension optimization to an actual infinite-energy limit. The weak-complement parity rotation is removed only at the level of entropy/coherent information, rather than identifying unrotated channel maps.
-- source:
--   Narrow Bounds for the Quantum Capacity of Thermal Attenuators, arXiv:1801.04731v5, PDF p. 6, Thermal optimization and infinite-energy reduction for the bosonic extension, (30)–(32)

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

/-- PDF pp.5-6, (29)-(32): Gaussian reduction, all-input fixed-energy thermal
optimality, and the actual infinite-energy limit for the constructed extension.
Parity in the weak complement affects no entropy; no channel-map equality with
an unrotated E_(1-eta),N is asserted. All thermal entropies are proved finite. -/
theorem bosonic_thermal_optimization (eta N : ℝ) (heta : (1 / 2 : ℝ) ≤ eta)
    (heta1 : eta < 1) (hN : 0 ≤ N) :
    WeaklyDegradable (bosonicExtension eta N)
      (extensionComplement (fockCoupling eta)
        (QAlgorithms.Papers.Independent.Claimed50.P35.thermalPurificationDensity N)) ∧
    traceClassQuantumCapacity (bosonicChannel eta N) ≤ singleLetter (bosonicExtension eta N) ∧
    singleLetter (bosonicExtension eta N) =
      (⨆ rho : {rho : State ℕ // entropyBits rho.coefficients < ⊤ ∧
          GaussianDensity rho.coefficients},
        ENNReal.ofReal (referenceCoherent (bosonicExtension eta N) rho.val.coefficients)) ∧
    (∀ n : ℝ, 0 ≤ n →
      IsDensity (thermalKernel n) ∧ entropyBits (thermalKernel n) < ⊤ ∧
      entropyBits (bosonicExtension eta N (thermalKernel n)) < ⊤ ∧
      entropyBits (extensionComplement (fockCoupling eta)
        (QAlgorithms.Papers.Independent.Claimed50.P35.thermalPurificationDensity N)
        (thermalKernel n)) < ⊤ ∧
      (∀ rho : State ℕ,
        weightedPhotonExpectation id rho.coefficients = ENNReal.ofReal n →
        entropyBits rho.coefficients < ⊤ ∧
        referenceCoherent (bosonicExtension eta N) rho.coefficients ≤
          referenceCoherent (bosonicExtension eta N) (thermalKernel n)) ∧
      referenceCoherent (bosonicExtension eta N) (thermalKernel n) =
        -referenceCoherent (mixedWeak (fockCoupling eta) (thermalKernel N)) (thermalKernel n) ∧
      referenceCoherent (bosonicExtension eta N) (thermalKernel n) =
        -referenceCoherent (bosonicChannel (1 - eta) N) (thermalKernel n)) ∧
    singleLetter (bosonicExtension eta N) < ⊤ ∧
    Tendsto (fun n : ℝ => referenceCoherent (bosonicExtension eta N) (thermalKernel n))
      atTop (𝓝 (singleLetter (bosonicExtension eta N)).toReal) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P15

end
