-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P15_complementary_coherent_information
-- name    : QAlgorithms.Papers.Independent.Bridge50.P15.complementary_coherent_information
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:26:31.648793+00:00
-- url     : https://prove2.me/theorems/fd0fe6f9-1063-4905-a067-7eb9d08ce149
-- title:
--   Complementary coherent-information identity, Eq. (26)
-- statement:
--   Let $U:A\otimes E\to B\otimes F$ be a unitary and $|\tau\rangle_{ER}$ a normalized purification of the environmental state. Let $\Phi^e:A\to BR$ and $\bar\Phi:A\to F$ be the two complementary channels obtained from the same pure environmental dilation. For every normalized input state $\rho$ of finite entropy,
--
--   $$J(\rho,\Phi^e)=-J(\rho,\bar\Phi).$$
--
--   Coherent information is $J(\rho,\Psi)=I(R_0:B)_\omega-S(\rho)$ in bits, using a reference purification $R_0$ of the input. This is well defined for finite input entropy even if receiver and complementary entropies are both infinite, and agrees with their entropy difference whenever both are finite. No weak-degradability hypothesis is needed. This identity exchanges the coherent information of the two actual complementary legs.
-- source:
--   Narrow Bounds for the Quantum Capacity of Thermal Attenuators, arXiv:1801.04731v5, PDF p. 5, Complementary coherent-information identity, Eq. (26)

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

/-- PDF pp.4-5, (24),(26): complementary coherent-information identity.
Finite input entropy is the reference definition's domain, with no finite-output
entropy restriction and no weak-degradability assumption. -/
theorem complementary_coherent_information
    {A B E F R : Type} [Nonempty A] [Nonempty B] [Nonempty E] [Nonempty F] [Nonempty R]
    (U : Hilbert (A × E) ≃ₗᵢ[ℂ] Hilbert (B × F))
    (tau : Hilbert (E × R)) (htau : ‖tau‖ = 1)
    (rho : State A) (hentropy : entropyBits rho.coefficients < ⊤) :
    referenceCoherent (purifiedExtension (isometryCoeff U.toLinearIsometry) (rankOne tau))
      rho.coefficients =
    -referenceCoherent (mixedWeak (isometryCoeff U.toLinearIsometry)
      (partialRight (rankOne tau))) rho.coefficients := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P15

end
