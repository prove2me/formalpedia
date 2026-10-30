-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P15_purified_environment_extension
-- name    : QAlgorithms.Papers.Independent.Bridge50.P15.purified_environment_extension
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:25:33.117331+00:00
-- url     : https://prove2.me/theorems/6d5fe3c4-cb01-4873-88fb-cfcfc22acbd4
-- title:
--   Purified environmental extension: degradability and capacity bound, (23)–(25)
-- statement:
--   Let $U:A\otimes E\to B\otimes F$ be a unitary between complete quantum-system Hilbert spaces, and let $|\tau\rangle_{ER}$ be a normalized purification of a fixed environmental state $\sigma_E$. For every input density operator $\rho$, compute the single joint output $\omega_{BFR}=(U\otimes I_R)(\rho\otimes|\tau\rangle\langle\tau|)(U^\dagger\otimes I_R)$. Define the original receiver $\Phi$, its weak complement $\bar\Phi$, and the extension $\Phi^e$ by retaining $B$, $F$, and $BR$, respectively. If $\bar\Phi$ can be recovered from $\Phi$ by one CPTP map valid for every input, then $\Phi^e$ and its true complement $\widetilde\Phi^e$ are CPTP and $\Phi^e$ is degradable. Moreover,
--
--   $$\operatorname{Tr}_R\Phi^e(\rho)=\Phi(\rho),\qquad \operatorname{Tr}_B\Phi^e(\rho)=\tau_R,\qquad \widetilde\Phi^e(\rho)=\bar\Phi(\rho),$$
--   $$Q(\Phi)\le Q(\Phi^e)=Q_1(\Phi^e).$$
--
--   Here $\tau_R=\operatorname{Tr}_E|\tau\rangle\langle\tau|$, $Q$ is unassisted quantum capacity in qubits per use, and $Q_1$ is the supremum of reference coherent information over all finite-input-entropy states. Every CPTP recovery $\Delta$ satisfying $\bar\Phi=\Delta\circ\Phi$ yields the explicit extension degrader $\Delta\circ\operatorname{Tr}_R$. The systems are nonzero and no separability, thermal or input-energy hypothesis is imposed. The unchanged local ancilla can remain correlated with the receiver, which is the reason this extension supplies a capacity upper bound.
-- source:
--   Narrow Bounds for the Quantum Capacity of Thermal Attenuators, arXiv:1801.04731v5, PDF p. 5, Purified environmental extension: degradability and capacity bound, (23)–(25)

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

/-- PDF pp.4-5, (22)-(25), and Discussion p.7: arbitrary mixed bath with one
normalized purification, including nonthermal baths. All channels and marginals
come from U and tau. Weak degradability is the only recovery hypothesis. -/
theorem purified_environment_extension
    {A B E F R : Type} [Nonempty A] [Nonempty B] [Nonempty E] [Nonempty F] [Nonempty R]
    (U : Hilbert (A × E) ≃ₗᵢ[ℂ] Hilbert (B × F))
    (tau : Hilbert (E × R)) (htau : ‖tau‖ = 1)
    (hweak : WeaklyDegradable
      (mixedReceiver (isometryCoeff U.toLinearIsometry) (partialRight (rankOne tau)))
      (mixedWeak (isometryCoeff U.toLinearIsometry) (partialRight (rankOne tau)))) :
    let K := isometryCoeff U.toLinearIsometry
    let sigma := partialRight (rankOne tau)
    let Phi := mixedReceiver K sigma
    let ext := purifiedExtension K (rankOne tau)
    let bar := mixedWeak K sigma
    IsTraceClassChannel ext ∧ IsTraceClassChannel (extensionComplement K (rankOne tau)) ∧
    (∀ rho : State A,
      partialRight (ext rho.coefficients) = Phi rho.coefficients ∧
      partialLeft (ext rho.coefficients) = partialLeft (rankOne tau) ∧
      extensionComplement K (rankOne tau) rho.coefficients = bar rho.coefficients) ∧
    WeaklyDegradable ext (extensionComplement K (rankOne tau)) ∧
    (∀ Delta : Operation B F, IsTraceClassChannel Delta →
      (∀ rho : State A, Delta (Phi rho.coefficients) = bar rho.coefficients) →
      IsTraceClassChannel (fun X : Matrix (B × R) (B × R) ℂ => Delta (partialRight X)) ∧
      ∀ rho : State A, Delta (partialRight (ext rho.coefficients)) =
        extensionComplement K (rankOne tau) rho.coefficients) ∧
    traceClassQuantumCapacity Phi ≤ traceClassQuantumCapacity ext ∧
    traceClassQuantumCapacity ext = singleLetter ext := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P15

end
