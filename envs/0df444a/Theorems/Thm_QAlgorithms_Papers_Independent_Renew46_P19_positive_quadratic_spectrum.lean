-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P19_positive_quadratic_spectrum
-- name    : QAlgorithms.Papers.Independent.Renew46.P19.positive_quadratic_spectrum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:27:29.675569+00:00
-- url     : https://prove2.me/theorems/1c9e0c21-280e-4899-b0cf-c596cfe74411
-- title:
--   Positive quadratic Hamiltonian spectral formula
-- statement:
--   Let $n\ge1$, $\hbar=1$, and $H(z)=\tfrac12 z^{\mathsf T}Mz$ for a real symmetric positive-definite $2n$ by $2n$ matrix $M$. Let $\omega_1,\ldots,\omega_n>0$ list the frequencies of $JM$, including multiplicities: its eigenvalues are $\pm i\omega_j$. The full spectra and point spectra of the natural weak L2 configuration Weyl and phase star realizations are
--
--   $$
--   \left\{\sum_{j=1}^n(N_j+\tfrac12)\omega_j:(N_1,\ldots,N_n)\in\mathbb N^n\right\}.
--   $$
--
--   No ordering of the frequencies, rational independence, or simplicity is assumed. The spectral set is independent of the inconsistent transport direction printed later on the page.
-- source:
--   A new approach to the star-genvalue equation, arXiv:0808.0489v1, PDF p. 11, §5, positive quadratic extension

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P19

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Renew46.P19

open QAlgorithms.Papers.Independent.Claimed50.P10 (Configuration coordinateDot)

open QAlgorithms.Papers.Independent.Claimed50.P37 (PhaseCoordinates Quadrature)

open QAlgorithms.Papers.Independent.Next46.P20
  (ConfigurationL2 PhaseL2 phasePosition phaseMomentum phasePoint)

open QAlgorithms.Papers.Independent.Claimed50.P05 (spectrumOf pointSpectrum)

open QAlgorithms.Papers.Independent.Frontier30.P10 (symplecticPair)

local notation "sigma" => fun {n : ℕ} (z w : PhaseCoordinates n) =>
  symplecticPair (Sum.elim (phasePosition z) (phaseMomentum z))
    (Sum.elim (phasePosition w) (phaseMomentum w))

/-- PDF pp.10–11: the positive quadratic spectral formula at hbar=1,
without selecting an inconsistent Williamson inverse or assuming simple levels. -/
theorem positive_quadratic_spectrum {n : ℕ} (hn : 0 < n)
    (M : Matrix (Quadrature n) (Quadrature n) ℝ) (hM : M.PosDef)
    (omega : Fin n → ℝ) (homega : HasFrequencies M omega) :
    spectrumOf (k := ℂ) (quadraticConfigurationGraph M) = quadraticLevels omega ∧
    spectrumOf (k := ℂ) (quadraticPhaseGraph M) = quadraticLevels omega ∧
    pointSpectrum (k := ℂ) (quadraticConfigurationGraph M) = quadraticLevels omega ∧
    pointSpectrum (k := ℂ) (quadraticPhaseGraph M) = quadraticLevels omega := by sorry

end QAlgorithms.Papers.Independent.Renew46.P19

end
