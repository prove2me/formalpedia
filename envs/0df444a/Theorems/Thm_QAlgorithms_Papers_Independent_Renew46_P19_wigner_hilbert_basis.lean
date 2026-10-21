-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P19_wigner_hilbert_basis
-- name    : QAlgorithms.Papers.Independent.Renew46.P19.wigner_hilbert_basis
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:25:40.270403+00:00
-- url     : https://prove2.me/theorems/c39f7e62-ab58-4192-a728-341194310898
-- title:
--   Double cross-Wigner family is a Hilbert basis
-- statement:
--   Let $n\ge1$, $\hbar>0$, and $(\phi_j)_{j\in I}$ be any Hilbert basis of $L^2(\mathbb R^n)$. The extended normalized window transforms are realized by their Wigner formulas, and
--
--   $$
--   \bigl(W_{\phi_j}\phi_k\bigr)_{(j,k)\in I\times I}
--   $$
--
--   is a Hilbert basis of $L^2(\mathbb R^{2n})$.
--
--   Both orthonormality and completeness are asserted; the basis vectors need not be Schwartz functions or eigenfunctions.
-- source:
--   A new approach to the star-genvalue equation, arXiv:0808.0489v1, PDF p. 7, Lemma 3

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

/-- PDF p.7, Lemma 3: arbitrary L2 Hilbert basis; the conclusion includes
completeness of the double-indexed family, with no Schwartz basis assumption. -/
theorem wigner_hilbert_basis {n : ℕ} (hn : 0 < n) (hbar : ℝ) (hhbar : 0 < hbar)
    {I : Type*} (basis : HilbertBasis I ℂ (ConfigurationL2 n)) :
    (∀ j, RealizesWindow hbar (basis j) (windowMap hbar (basis j))) ∧
    ∃ B : HilbertBasis (I × I) ℂ (PhaseL2 n),
      ∀ j k, B (j, k) = windowMap hbar (basis j) (basis k) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P19

end
