-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P19_harmonic_oscillator_spectrum
-- name    : QAlgorithms.Papers.Independent.Renew46.P19.harmonic_oscillator_spectrum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:26:22.008853+00:00
-- url     : https://prove2.me/theorems/d6ba8631-6966-4600-ac89-c6579481df15
-- title:
--   Harmonic oscillator spectra and normalized Hermite functions
-- statement:
--   Set $n=1$, $\hbar=1$, and $H(x,p)=(x^2+p^2)/2$. Give the configuration Weyl operator and phase star differential operator their maximal weak L2 realizations. Both their spectra and point spectra are
--
--   $$
--   \{k+\tfrac12:k\in\mathbb N\}.
--   $$
--
--   For each $k$, the configuration operator has a normalized eigenfunction, at eigenvalue $k+1/2$, represented by
--
--   $$
--   \psi_k(x)=(2^k k!\sqrt\pi)^{-1/2}e^{-x^2/2}H_k(x),\qquad
--   H_k(x)=(-1)^ke^{x^2}\frac{d^k}{dx^k}e^{-x^2}.
--   $$
--
--   This identifies the spectral sets and the explicitly normalized configuration eigenfunctions. It does not assert simple phase eigenspaces.
-- source:
--   A new approach to the star-genvalue equation, arXiv:0808.0489v1, PDF p. 10, §5, (18)–(19)

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

/-- PDF p.10, (18)–(19): both full spectra and point spectra, and the
normalized Hermite eigenfunctions. The unexplained Rodrigues m is corrected. -/
theorem harmonic_oscillator_spectrum :
    let M : Matrix (Quadrature 1) (Quadrature 1) ℝ := 1
    let levels : Set ℂ := {lambda | ∃ k : ℕ, lambda = ((k : ℝ) + 1 / 2 : ℝ)}
    spectrumOf (k := ℂ) (quadraticConfigurationGraph M) = levels ∧
    spectrumOf (k := ℂ) (quadraticPhaseGraph M) = levels ∧
    pointSpectrum (k := ℂ) (quadraticConfigurationGraph M) = levels ∧
    pointSpectrum (k := ℂ) (quadraticPhaseGraph M) = levels ∧
    (∀ k : ℕ, ∃ psi : ConfigurationL2 1,
      (∀ᵐ x : Configuration 1, psi x = hermiteFunction k x) ∧ ‖psi‖ = 1 ∧
      (psi, (((k : ℝ) + 1 / 2 : ℝ) : ℂ) • psi) ∈ quadraticConfigurationGraph M) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P19

end
