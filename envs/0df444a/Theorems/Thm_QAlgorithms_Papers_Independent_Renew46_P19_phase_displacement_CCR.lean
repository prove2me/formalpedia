-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P19_phase_displacement_CCR
-- name    : QAlgorithms.Papers.Independent.Renew46.P19.phase_displacement_CCR
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:21:37.229544+00:00
-- url     : https://prove2.me/theorems/ffc75aec-15a1-4b3b-aea7-f7b1b55b111d
-- title:
--   Phase displacement multiplication and commutation
-- statement:
--   Let $n\ge1$ and $\hbar>0$. For $z=(x,p)$ and $w=(x',p')$ in $\mathbb R^{2n}$ put $\sigma(z,w)=p\cdot x'-p'\cdot x$. Define $\widetilde T(d)F(z)=e^{-i\sigma(z,d)/\hbar}F(z-d/2)$. For all displacements $d,e$,
--
--   $$
--   \widetilde T(d+e)=e^{-i\sigma(d,e)/(2\hbar)}\widetilde T(d)\widetilde T(e),\qquad
--   \widetilde T(e)\widetilde T(d)=e^{-i\sigma(d,e)/\hbar}\widetilde T(d)\widetilde T(e).
--   $$
--
--   These identities fix the central sign of the phase-space Heisenberg representation.
-- source:
--   A new approach to the star-genvalue equation, arXiv:0808.0489v1, PDF p. 5, §3, (10)–(11)

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

/-- PDF p.5, (10)–(11): both phase displacement laws, with the printed signs. -/
theorem phase_displacement_CCR {n : ℕ} (hn : 0 < n) (hbar : ℝ) (hhbar : 0 < hbar)
    (d e : PhaseCoordinates n) (f : PhaseCoordinates n → ℂ) (z : PhaseCoordinates n) :
    phaseShift hbar (d + e) f z =
      Complex.exp (-Complex.I * ((sigma d e / (2 * hbar) : ℝ) : ℂ)) *
        phaseShift hbar d (phaseShift hbar e f) z ∧
    phaseShift hbar e (phaseShift hbar d f) z =
      Complex.exp (-Complex.I * ((sigma d e / hbar : ℝ) : ℂ)) *
        phaseShift hbar d (phaseShift hbar e f) z := by sorry

end QAlgorithms.Papers.Independent.Renew46.P19

end
