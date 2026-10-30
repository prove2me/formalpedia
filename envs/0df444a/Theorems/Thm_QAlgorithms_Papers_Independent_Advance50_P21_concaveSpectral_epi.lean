-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P21_concaveSpectral_epi
-- name    : QAlgorithms.Papers.Independent.Advance50.P21.concaveSpectral_epi
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:47:58.67024+00:00
-- url     : https://prove2.me/theorems/15bf11c4-da37-4ddf-9f14-e8f9d340ca01
-- title:
--   Theorem 4: EPI for every concave spectral state function (seed headline)
-- statement:
--   Let $d\ge1$, let $\rho,\sigma$ be positive semidefinite complex $d\times d$ matrices of trace one, and let $a\in[0,1]$. Write
--   $$
--   \rho\boxplus_a\sigma=a\rho+(1-a)\sigma-i\sqrt{a(1-a)}(\rho\sigma-\sigma\rho).
--   $$
--
--   Suppose $f$ is a real-valued concave function on the state space that depends only on the multiset of eigenvalues. Then
--   $$f(\rho\boxplus_a\sigma)\ge a f(\rho)+(1-a)f(\sigma).$$
--   No continuity or differentiability of $f$ is assumed. This is the main qudit EPI for the full class in Definition 3.
-- source:
--   Entropy power inequalities for qudits, arXiv:1503.04213v3, PDF p. 6, Theorem 4: EPI for every concave spectral state function (seed headline)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P21

open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)

open QAlgorithms.Papers.Independent.Dependency50.P16 (simplex orderedSpectrum majorizedBy)

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble)

open QAlgorithms.Papers.Independent.Information100.P49 (thermalEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P11 (thermalEntropyInverse)

/-- PDF p.6, Theorem 4 (restated pp.11–12): EPI for every function in Definition 3. -/
theorem concaveSpectral_epi {d : ℕ} (hd : 0 < d) (f : Mat d → ℝ)
    (hf : ConcaveSpectralClass f) (rho sigma : Mat d)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    a * f rho + (1 - a) * f sigma ≤ f (quditAddition a rho sigma) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P21

end
