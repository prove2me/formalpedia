-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P26_pure_input_spectral_reduction
-- name    : QAlgorithms.Papers.Independent.Gap48.P26.pure_input_spectral_reduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:55:26.136112+00:00
-- url     : https://prove2.me/theorems/2be11c60-74ea-4b6d-ae1b-2ddb3238d0c1
-- title:
--   Pure-input spectral reduction through attenuation
-- statement:
--   Fix a finite gain $\kappa\ge1$, its quantum-limited amplifier $\mathcal A_\kappa$, and the quantum-limited attenuator $\mathcal E_\eta$ with $\eta=(\kappa-1)/\kappa$. For every unit Fock vector $\psi$ of finite mean energy, there is a bounded partial isometry $V$, which may depend on $\psi$, such that, putting $X=\mathcal A_\kappa\mathcal E_\eta(|\psi\rangle\langle\psi|)$,
--
--   $$V^*VX=X,\qquad \mathcal A_\kappa(|\psi\rangle\langle\psi|)=VXV^*.$$
--
--   The equality retains all nonzero spectral mass and therefore the output entropy.
--
--   **Source correction.** The printed full-space unitary is replaced by a support-preserving connecting partial isometry. The literal unitary claim fails for $\psi=|1\rangle$, $\kappa=2$ because the kernel dimensions differ. The source-cited supporting original, arXiv:1312.2251v1, §6, explicitly gives the partial-isometry form.
-- source:
--   Ultimate communication capacity of quantum optical channels by solving the Gaussian minimum-entropy conjecture, arXiv:1312.6225v1, PDF p. 3, Eq. (6), Fig. 3; source correction

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

/-- PDF p.3, (6), Fig.3: source-corrected spectral reduction. Printed unitary U
is replaced by a connecting partial isometry preserving the source support.
For |1> and kappa=2 the two outputs have different kernel dimensions; the
literal unitary assertion is false. The corrected form is independently explicit
in arXiv:1312.2251v1, Section 6, (35),(39), PDF pp.15-16. -/
theorem pure_input_spectral_reduction
    (A L : Operation ℕ ℕ) (kappa : ℝ) (hk : 1 ≤ kappa)
    (hA : PhaseInsensitive A kappa (kappa - 1))
    (hL : PhaseInsensitive L ((kappa - 1) / kappa) (1 - (kappa - 1) / kappa))
    (u : Hilbert ℕ) (hu : ‖u‖ = 1) (he : weightedPhotonExpectation id (rankOne u) < ⊤) :
    ∃ V : B.FockOperator, IsPartialIsometry V ∧
      PreservesSupport V (A (L (rankOne u))) ∧
      A (rankOne u) = conjugateKernel (operatorCoeff V) (A (L (rankOne u))) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P26

end
