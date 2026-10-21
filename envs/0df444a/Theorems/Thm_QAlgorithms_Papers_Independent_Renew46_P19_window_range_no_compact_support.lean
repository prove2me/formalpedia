-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P19_window_range_no_compact_support
-- name    : QAlgorithms.Papers.Independent.Renew46.P19.window_range_no_compact_support
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:28:51.103329+00:00
-- url     : https://prove2.me/theorems/9c4b8674-cce1-4257-a6f6-a113c7e80805
-- title:
--   No nonzero compactly supported vector in a fixed window range
-- statement:
--   Let $n\ge1$, $\hbar>0$, and fix a unit window $\phi\in L^2(\mathbb R^n)$. Its bounded window transform realizes the normalized Wigner formula. If $\Psi\in\mathcal H_\phi=\operatorname{ran}W_\phi$ and some $R>0$ satisfies $\Psi(z)=0$ for almost every $z$ with $|z|\ge R$, then
--
--   $$
--   \Psi=0\quad\text{in }L^2(\mathbb R^{2n}).
--   $$
--
--   Thus a fixed window range contains no nonzero vector with compact essential support.
-- source:
--   A new approach to the star-genvalue equation, arXiv:0808.0489v1, PDF p. 12, §6, consequence after (21)

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

/-- PDF p.12: each fixed unit-window range has no nonzero compactly supported
L2 vector. Compact support is stated as essential vanishing outside a ball. -/
theorem window_range_no_compact_support {n : ℕ} (hn : 0 < n) (hbar : ℝ) (hhbar : 0 < hbar)
    (phi : ConfigurationL2 n) (hphi : ‖phi‖ = 1) (Psi : PhaseL2 n)
    (hRange : Psi ∈ windowRange hbar phi)
    (hSupport : ∃ R : ℝ, 0 < R ∧ ∀ᵐ z : PhaseCoordinates n,
      R ^ 2 ≤ radiusSquared z → Psi z = 0) :
    RealizesWindow hbar phi (windowMap hbar phi) ∧ Psi = 0 := by sorry

end QAlgorithms.Papers.Independent.Renew46.P19

end
