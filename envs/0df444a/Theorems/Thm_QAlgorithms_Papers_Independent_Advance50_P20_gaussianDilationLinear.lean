-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P20_gaussianDilationLinear
-- name    : QAlgorithms.Papers.Independent.Advance50.P20.gaussianDilationLinear
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:28:00.99433+00:00
-- url     : https://prove2.me/theorems/5a9b11d7-b8ad-418b-998a-a4e4501d9ac2
-- title:
--   Gaussian dilations are linear Bosonic channels
-- statement:
--   Let a finite-mode system and a finite-mode environment have their complete Fock Hilbert spaces. Fix a Gaussian unitary $U$, an arbitrary normalized environment density $\sigma$, and independent Weyl representations. Write $S$ for the source's inverse symplectic transformation, with blocks $S_{11},S_{12},S_{21},S_{22}$, and allow a displacement phase $e^{i d\cdot(\xi,\eta)}$. Define $\Phi(\rho)=\operatorname{Tr}_E U(\rho\otimes\sigma)U^\dagger$. Then $\Phi$ is completely positive and trace preserving, and every trace-class input obeys
--
--   $$\chi_{\Phi(\rho)}(\xi)=\chi_\rho(S_{11}\xi) f(\xi),\qquad f(\xi)=e^{i d_S\cdot\xi}\chi_\sigma(S_{21}\xi).$$
--
--   Thus every Gaussian-dilatable channel, including the photon-added examples, is linear Bosonic. No Gaussianity of $\sigma$ is required. In the centered representative $d_S=0$.
--
--   **Formalization Note** The accepted linear-Bosonic predicate uses $K^{\mathsf T}\xi$, so the formal parameter is $K=S_{11}^{\mathsf T}$.
-- source:
--   Non-Gaussian operations on bosonic modes of light: Photon-added Gaussian channels, arXiv:1604.07859v4, PDF p. 3, Proposition 1

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

/-- Proposition 1, PDF p.3, Eqs.(5)--(10): every finite-mode Gaussian dilation
is linear Bosonic. K is S11 transpose because the accepted predicate uses K^T.
Displaced Gaussian couplings retain their scalar Weyl phase in the multiplier. -/
theorem gaussianDilationLinear {s t : ℕ}
    (W : ScaledWeylRepresentation (Fin s → ℕ) s 1)
    (V : ScaledWeylRepresentation (Fin t → ℕ) t 1)
    (U : Hilbert ((Fin s → ℕ) × (Fin t → ℕ)) ≃ₗᵢ[ℂ]
      Hilbert ((Fin s → ℕ) × (Fin t → ℕ)))
    (S : Matrix (JointPhaseIndex s t) (JointPhaseIndex s t) ℝ)
    (d : JointPhaseIndex s t → ℝ) (hU : GaussianCoupling W V U S d)
    (sigma : State (Fin t → ℕ)) :
    IsTraceClassChannel (dilationReceiver U sigma.coefficients) ∧
    LinearBosonic W W (dilationReceiver U sigma.coefficients)
      (S.submatrix Sum.inl Sum.inl).transpose
      (fun z => Complex.exp (Complex.I * ((dotProduct (d ∘ Sum.inl) z : ℝ) : ℂ)) *
        weylTraceCharacteristic V sigma.coefficients ((S.submatrix Sum.inr Sum.inl).mulVec z)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P20

end
