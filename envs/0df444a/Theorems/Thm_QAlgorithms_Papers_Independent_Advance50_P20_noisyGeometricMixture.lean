-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P20_noisyGeometricMixture
-- name    : QAlgorithms.Papers.Independent.Advance50.P20.noisyGeometricMixture
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:34:29.035568+00:00
-- url     : https://prove2.me/theorems/11a4d000-6292-40f7-b3ef-c2a9670df9fb
-- title:
--   Noisy canonical channels are geometric mixtures of photon-added channels
-- statement:
--   Let $\mathcal H=\ell^2(\mathbb N)$, with normalized number states $|j\rangle$, and let $n\in\mathbb N$ be the environment photon number. Write $A(\kappa;n)$, $B(\kappa;n)$ and $C(\kappa;n)$ for the canonical amplifier, attenuator and phase-conjugator channels, respectively. Their amplitude domains are $\kappa\ge1$, $0\le\kappa\le1$ and $\kappa\ge0$. Each channel is defined by its specified two-mode unitary, the product environment $|n\rangle\langle n|$, and the environmental partial trace. All density operators are positive trace class with trace one, and all Hilbert spaces are untruncated.
--
--   Fix one canonical coupling and a finite thermal mean $\bar N\ge0$. Let $\Phi_{\bar N}$ be the channel using that coupling with the thermal environment, and let $\Phi_n$ use $|n\rangle\langle n|$. The weights $p_n=\bar N^n/(1+\bar N)^{n+1}$ are nonnegative and sum to one, and
--
--   $$\Phi_{\bar N}(X)=\sum_{n=0}^\infty p_n\Phi_n(X)$$
--
--   in trace norm for every trace-class $X$. In standard displacement coordinates with vacuum characteristic $e^{-|z|^2/2}$, the channel is identified by
--
--   $$\chi_{\Phi_{\bar N}(\rho)}(z)=\chi_\rho(Xz)\exp\!\left[-\frac{(2\bar N+1)Y_{\rm QL}|z|^2}{2}\right].$$
--
--   Here $Xz=\kappa z$ and $Y_{\rm QL}=\kappa^2-1$ for the amplifier, $Xz=\kappa z$ and $Y_{\rm QL}=1-\kappa^2$ for attenuation, and $Xz=-\kappa\bar z$ and $Y_{\rm QL}=1+\kappa^2$ for conjugation. Thus the extra noise is $2\bar N Y_{\rm QL}$. This states the three canonical constructions, including the vacuum and identity limits.
-- source:
--   Non-Gaussian operations on bosonic modes of light: Photon-added Gaussian channels, arXiv:1604.07859v4, PDF p. 14, Proposition 15

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

/-- Proposition 15, PDF pp.13--14, Eqs.(43)--(47): geometric convex mixture
for the three canonical families, on all trace-class inputs. The thermal Weyl
law identifies extra noise as 2*N*Y_QL and keeps the source's factor 1/2. -/
theorem noisyGeometricMixture (c : PhotonFamily) (k : ℝ) (hk : PhotonParameter c k)
    (N : ℝ) (hN : 0 ≤ N) :
    DilationRealized c k ∧ IsDensity (thermalKernel N) ∧
    IsTraceClassChannel (canonicalThermalChannel c k N) ∧
    (∀ n, 0 ≤ thermalProbability N n) ∧ HasSum (thermalProbability N) 1 ∧
    (∀ X, IsTraceClass X →
      TraceSeries (fun n => (thermalProbability N n : ℂ) • photonChannel c k n X)
        (canonicalThermalChannel c k N X)) ∧
    ∀ rho : State ℕ, ∀ z : ℂ,
      QAlgorithms.Papers.Independent.Frontier30.P14.weylCharacteristic
        (canonicalThermalChannel c k N rho.coefficients) z =
      QAlgorithms.Papers.Independent.Frontier30.P14.weylCharacteristic rho.coefficients
        (canonicalArgument c k z) *
      Complex.exp (((-(2 * N + 1) * quantumLimitedNoise c k * Complex.normSq z / 2 : ℝ) : ℂ)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P20

end
