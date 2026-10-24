-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P50_lemma_5_4
-- name    : QAlgorithms.Papers.Independent.Information100.P50.lemma_5_4
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:04:16.544315+00:00
-- url     : https://prove2.me/theorems/45ca5d76-d7bb-4881-a251-b1219b98423f
-- title:
--   Lemma 5.4: For effects E,Eprime and 0<alpha<1, specNorm(h_alpha(E)-h_alpha(Eprime))≤specNorm(E-Eprime)^alpha+specNorm(E-E
-- statement:
--   All spaces are finite-dimensional complex Euclidean spaces. Input and output dimensions are positive wherever states or extreme eigenvalues occur. The Choi matrix $J$ is unnormalized and has output factor first. Write $\|\Theta\|_\diamond$ for the full completely bounded trace norm, $\|A\|_\infty$ for the operator norm, and $\Theta^*$ for the Hilbert–Schmidt adjoint.
--
--   For $0<\alpha<1$, define $h_\alpha(t)=t^\alpha(1-t)^{1-\alpha}$ on $[0,1]$, with zero endpoint values. For any two effects $E,E'$,
--
--   $$\|h_\alpha(E)-h_\alpha(E')\|_\infty\le\|E-E'\|_\infty^\alpha+\|E-E'\|_\infty^{1-\alpha}.$$
--
--   Both terms have coefficient one. This is the explicit operator modulus used for the Renyi quasi-entropy estimate.
-- source:
--   Quantitative upper bounds for certain quantum channel divergences, arXiv:2610.16270v1, PDF p. 18, Lemma 5.4

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50

noncomputable section

open scoped Matrix ComplexConjugate ENNReal Topology ComplexOrder Kronecker

open Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P50

/-- Lemma 5.4, source PDF p.18, retaining both powers and unit coefficients. -/
theorem lemma_5_4 {n : ℕ} (E F : M n) (hE : IsEffect E) (hF : IsEffect F)
    (alpha : ℝ) (halpha : 0 < alpha) (halpha1 : alpha < 1) :
    specNorm (cfc (hAlpha alpha) E - cfc (hAlpha alpha) F) ≤
      Real.rpow (specNorm (E - F)) alpha + Real.rpow (specNorm (E - F)) (1 - alpha) := by sorry

end QAlgorithms.Papers.Independent.Information100.P50

end
