-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P19_window_range_closed
-- name    : QAlgorithms.Papers.Independent.Renew46.P19.window_range_closed
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:23:13.150112+00:00
-- url     : https://prove2.me/theorems/71511de5-c758-4a6c-8a00-ff2c36e7b191
-- title:
--   Closed Hilbert range of a unit Schwartz window
-- statement:
--   Let $n\ge1$, $\hbar>0$, and let $\phi\in\mathcal S(\mathbb R^n)$ have $L^2$ norm one. Give $\mathcal H_\phi=\operatorname{ran}W_\phi$ the inherited norm and inner product. Then
--
--   $$
--   \mathcal H_\phi\text{ is closed in }L^2(\mathbb R^{2n})\text{ and is complete.}
--   $$
--
--   Thus the window range is a Hilbert space in its inherited structure.
-- source:
--   A new approach to the star-genvalue equation, arXiv:0808.0489v1, PDF p. 5, Proposition 1

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

/-- PDF p.5, Proposition 1: actual range closedness and completeness with the
inherited Hilbert norm. Neither the projection nor a left inverse is assumed. -/
theorem window_range_closed {n : ℕ} (hn : 0 < n) (hbar : ℝ) (hhbar : 0 < hbar)
    (phi : SchwartzMap (Configuration n) ℂ)
    (hphi : ‖phi.toLp 2 (volume : Measure (Configuration n))‖ = 1) :
    let phiL2 := phi.toLp 2 (volume : Measure (Configuration n))
    IsClosed (windowRange hbar phiL2 : Set (PhaseL2 n)) ∧
      CompleteSpace (windowRange hbar phiL2) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P19

end
