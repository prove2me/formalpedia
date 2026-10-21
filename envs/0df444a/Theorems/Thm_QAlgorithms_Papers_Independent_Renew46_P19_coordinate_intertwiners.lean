-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P19_coordinate_intertwiners
-- name    : QAlgorithms.Papers.Independent.Renew46.P19.coordinate_intertwiners
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:24:39.170972+00:00
-- url     : https://prove2.me/theorems/3598a125-d32e-4b04-9e3d-0420b3bc5dc3
-- title:
--   Both coordinate star intertwiners
-- statement:
--   Let $n\ge1$, $\hbar>0$, and $\psi,\phi\in\mathcal S(\mathbb R^n)$ with $\|\phi\|_2=1$. For every coordinate $j$,
--
--   $$
--   x_j\star W_\phi\psi=(x_j+i\hbar\partial_{p_j}/2)W_\phi\psi=W_\phi(x_j\psi),
--   $$
--   $$
--   p_j\star W_\phi\psi=(p_j-i\hbar\partial_{x_j}/2)W_\phi\psi=W_\phi(-i\hbar\partial_{x_j}\psi).
--   $$
--
--   These identities specify both Bopp shifts, with their derivative directions and signs, on the Schwartz domain.
-- source:
--   A new approach to the star-genvalue equation, arXiv:0808.0489v1, PDF p. 6, §3, coordinate displays

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

/-- PDF p.6, both coordinate star intertwiners on Schwartz inputs.
coordinateStar expands to x+i*hbar*d_p/2 and p-i*hbar*d_x/2. -/
theorem coordinate_intertwiners {n : ℕ} (hn : 0 < n) (hbar : ℝ) (hhbar : 0 < hbar)
    (psi phi : SchwartzMap (Configuration n) ℂ)
    (hphi : ‖phi.toLp 2 (volume : Measure (Configuration n))‖ = 1)
    (j : Fin n) (z : PhaseCoordinates n) :
    coordinateStar hbar 0 j (windowFormula hbar psi phi) z =
      windowFormula hbar (fun x => (x j : ℂ) * psi x) phi z ∧
    coordinateStar hbar 1 j (windowFormula hbar psi phi) z =
      windowFormula hbar (fun x => -Complex.I * (hbar : ℂ) *
        (fderiv ℝ (psi : Configuration n → ℂ) x) (Pi.single j 1)) phi z := by sorry

end QAlgorithms.Papers.Independent.Renew46.P19

end
