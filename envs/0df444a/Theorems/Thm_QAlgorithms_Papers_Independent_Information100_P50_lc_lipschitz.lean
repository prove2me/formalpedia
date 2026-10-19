-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P50_lc_lipschitz
-- name    : QAlgorithms.Papers.Independent.Information100.P50.lc_lipschitz
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:10:16.235374+00:00
-- url     : https://prove2.me/theorems/41695bf0-bb4a-48f5-bb7c-976805123c9f
-- title:
--   Unnumbered §6 Vincze–Le Cam Lipschitz estimate: For effects E,Eprime, specNorm(h_LC(E)-h_LC(Eprime))≤4*specNorm(E-Eprime), h_LC(t)=(2t-1)^2
-- statement:
--   All spaces are finite-dimensional complex Euclidean spaces. Input and output dimensions are positive wherever states or extreme eigenvalues occur. The Choi matrix $J$ is unnormalized and has output factor first. Write $\|\Theta\|_\diamond$ for the full completely bounded trace norm, $\|A\|_\infty$ for the operator norm, and $\Theta^*$ for the Hilbert–Schmidt adjoint.
--
--   For any two effects $E,E'$ on the same finite space, with $h_{LC}(t)=(2t-1)^2$,
--
--   $$\|h_{LC}(E)-h_{LC}(E')\|_\infty\le4\|E-E'\|_\infty.$$
--
--   The coefficient is independent of dimension, and no mutual commutativity is required. This is the conclusion's explicit Vincze–Le Cam Lipschitz estimate.
-- source:
--   Quantitative upper bounds for certain quantum channel divergences, arXiv:2610.16270v1, PDF p. 24, Unnumbered §6 Vincze–Le Cam Lipschitz estimate

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50

noncomputable section

open scoped Matrix ComplexConjugate ENNReal Topology ComplexOrder Kronecker

open Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P50

/-- Unnumbered Section 6 Vincze–Le Cam estimate, source PDF p.24.
The constant is 4 in every dimension, with no commutativity assumption. -/
theorem lc_lipschitz {n : ℕ} (E F : M n) (hE : IsEffect E) (hF : IsEffect F) :
    specNorm (cfc (convexPerspective lcGenerator) E - cfc (convexPerspective lcGenerator) F) ≤
      4 * specNorm (E - F) := by sorry

end QAlgorithms.Papers.Independent.Information100.P50

end
