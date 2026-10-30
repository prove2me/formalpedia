-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P20_noisyVacuumPreparation
-- name    : QAlgorithms.Papers.Independent.Advance50.P20.noisyVacuumPreparation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:38:43.209077+00:00
-- url     : https://prove2.me/theorems/1b417124-eb00-4414-832e-103680f10024
-- title:
--   Two vacuum environment modes and a squeezer realize the noisy canonical channels
-- statement:
--   Fix a canonical amplifier, attenuator, or phase conjugator with its amplitude parameter in the source domain, and a finite thermal mean $N\ge0$. Start the two environment modes in $|0,0\rangle$ and apply the specified two-mode squeeze unitary $U_A(\sqrt{1+N})$. The prepared unit vector is $|\Psi_{N,0}\rangle=\sum_{j\ge0}\sqrt{N^j/(1+N)^{j+1}}|j,j\rangle$, whose first-mode reduced state is the thermal density $\theta_N$. Applying the canonical channel unitary to the carrier and first environment mode, leaving the second mode untouched and then tracing both environment modes, gives exactly the thermal-environment noisy channel on every trace-class input. The resulting map is CPTP, and $N=0$ is included.
-- source:
--   Non-Gaussian operations on bosonic modes of light: Photon-added Gaussian channels, arXiv:1604.07859v4, PDF p. 14, Proposition 16

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P20

noncomputable section

open Filter MeasureTheory

open scoped BigOperators Topology ENNReal

namespace QAlgorithms.Papers.Independent.Advance50.P20

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity IsTraceClass IsTraceClassChannel rankOne productCoeff traceSize)

open QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock FockOperator fockKet fockDyad HasFockMatrix operatorOfMatrix KrausComplete
    CoherentRealized IsClassical husimiQ)

open QAlgorithms.Papers.Independent.Frontier18.P18
  (operatorCoeff boundedOperator conjugateCoeff IsKrausRepresentation)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation unitaryCoeff conjugateKernel partialRight partialLeft dilationReceiver weakComplement
    boundedUnitaryConjugation traceClassTensorPower operationalTraceClassCapacity)

open QAlgorithms.Papers.Independent.Claimed50.P35
  (InterleavedPhase ScaledWeylRepresentation physicalCommutationMatrix
    weylTraceCharacteristic LinearBosonic)

-- Accepted extended bit entropy and mean-photon thermal coefficients.

open QAlgorithms.Papers.Independent.Gap48.P26 (entropyBits thermalKernel)

open QAlgorithms.Papers.Independent.Claimed50.P39 (thermalProbability)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 16, PDF p.14, with Fig.16 on p.15 (attributed there to Ref.[55]):
prepare two vacuum modes by the actual Eq.(11) squeezer of gain sqrt(1+N),
then apply the canonical channel unitary to the carrier and first environment.
The prepared vector, its thermal marginal, and equality of the resulting
three-mode implementation are conclusions. No arbitrary purification hypothesis
replaces the specified squeeze transformation. N=0 retains the vacuum case. -/
theorem noisyVacuumPreparation (c : PhotonFamily) (k : ℝ)
    (hk : PhotonParameter c k) (N : ℝ) (hN : 0 ≤ N) :
    DilationRealized c k ∧
    DilationRealized .amplifier (Real.sqrt (1 + N)) ∧
    addedPurification N 0 =
      dilationUnitary .amplifier (Real.sqrt (1 + N))
        (lp.single 2 (0, 0) (1 : ℂ)) ∧
    ‖addedPurification N 0‖ = 1 ∧
    IsDensity (rankOne (addedPurification N 0)) ∧
    partialRight (rankOne (addedPurification N 0)) = thermalKernel N ∧
    IsTraceClassChannel (pureAddedNoisyChannel c k N 0) ∧
    ∀ X, IsTraceClass X →
      pureAddedNoisyChannel c k N 0 X = canonicalThermalChannel c k N X := by sorry

end QAlgorithms.Papers.Independent.Advance50.P20

end
