-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P26_gaussian_unitary_minimum_extension
-- name    : QAlgorithms.Papers.Independent.Gap48.P26.gaussian_unitary_minimum_extension
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:01:38.524016+00:00
-- url     : https://prove2.me/theorems/d986a6a1-326c-49a6-a2a3-567a06442c80
-- title:
--   Gaussian-unitary normal-form minimum entropy
-- statement:
--   Let $\Phi$ be a physical phase-insensitive single-mode Gaussian channel of finite parameters, and let $U,V$ be fixed single-mode Gaussian unitaries, allowing squeezing and displacement. Put $\Psi=\mathcal U\circ\Phi\circ\mathcal V$, where the superoperators conjugate by $U$ and $V$. For $m\ge1$, write $s_m$ for the minimum over normalized pure finite-total-energy inputs, and set $\rho_*=V^*|0\rangle\langle0|V$. Then
--
--   $$s_m(\Psi)=m s_1(\Psi)=mS(\Psi(\rho_*))=S(\Psi^{\otimes m}(\rho_*^{\otimes m})).$$
--
--   Thus the inverse input unitary determines the minimizing Gaussian seed. The assertion concerns exactly this constructed normal-form class, without quantifying over the unspecified exceptions to the source normal-form classification.
-- source:
--   Ultimate communication capacity of quantum optical channels by solving the Gaussian minimum-entropy conjecture, arXiv:1312.6225v1, PDF p. 7, Gaussian channel normal-form paragraph; PDF p.4

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P26

open MeasureTheory Filter

open scoped ENNReal Topology BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Next46.P32 (NumberString vacuum)

open QAlgorithms.Papers.Independent.Next46.P45 (entanglementOfFormation)

open QAlgorithms.Papers.Independent.Dependency50.P30 (thermalEntropyBits)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State rankOne IsDensity IsBarycenter IsTraceClassChannel)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation traceClassTensorPower weylCharacteristic boundedUnitaryConjugation
   conjugateKernel partialRight GaussianDensity)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.4,7: minimum-entropy extension precisely for the constructed normal
form. The minimizing input is V-inverse of vacuum, not V of vacuum. -/
theorem gaussian_unitary_minimum_extension
    (Phi : Operation ℕ ℕ) (tau y : ℝ) (hPhi : PhaseInsensitive Phi tau y)
    (U V : Hilbert ℕ ≃ₗᵢ[ℂ] Hilbert ℕ)
    (hU : AffineGaussianUnitary U) (hV : AffineGaussianUnitary V) (m : ℕ) (hm : 0 < m) :
    let Psi := normalFormChannel Phi U V
    let seed := boundedUnitaryConjugation V.symm vacuumOne
    minimumFiniteEnergy totalPhotons (traceClassTensorPower Psi m) =
      (m : ℝ≥0∞) * minimumFiniteEnergy id Psi ∧
    minimumFiniteEnergy totalPhotons (traceClassTensorPower Psi m) =
      (m : ℝ≥0∞) * entropyBits (Psi seed) ∧
    minimumFiniteEnergy totalPhotons (traceClassTensorPower Psi m) =
      entropyBits (traceClassTensorPower Psi m
        (fun a b => ∏ j : Fin m, seed (a j) (b j))) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P26

end
