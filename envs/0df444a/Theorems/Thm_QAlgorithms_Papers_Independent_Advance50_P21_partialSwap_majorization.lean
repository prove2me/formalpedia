-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P21_partialSwap_majorization
-- name    : QAlgorithms.Papers.Independent.Advance50.P21.partialSwap_majorization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:55:09.697763+00:00
-- url     : https://prove2.me/theorems/b6d052bc-db8f-4531-be9e-a500477eed9f
-- title:
--   Theorem 11: spectral majorization
-- statement:
--   Let $d\ge1$, let $\rho,\sigma$ be positive semidefinite complex $d\times d$ matrices of trace one, and let $a\in[0,1]$. Write
--   $$
--   \rho\boxplus_a\sigma=a\rho+(1-a)\sigma-i\sqrt{a(1-a)}(\rho\sigma-\sigma\rho).
--   $$
--
--   Let $\lambda(\tau)$ denote the eigenvalues of a state $\tau$ in nonincreasing order. Then
--   $$\lambda(\rho\boxplus_a\sigma)\prec a\lambda(\rho)+(1-a)\lambda(\sigma).$$
--   Here $u\prec v$ means that the sum of the $k$ largest coordinates of $u$ is at most the corresponding sum for $v$, for every $k$, with equality for the total sum. This spectral majorization is the structural input to the main EPI.
-- source:
--   Entropy power inequalities for qudits, arXiv:1503.04213v3, PDF p. 11, Theorem 11: spectral majorization

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

/-- PDF p.11, Theorem 11, (5.1): ordinary spectral majorization, with both input spectra sorted. -/
theorem partialSwap_majorization {d : ℕ} (hd : 0 < d) (rho sigma : Mat d)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    majorizedBy (decreasingStateSpectrum (quditAddition a rho sigma))
      (a • decreasingStateSpectrum rho + (1 - a) • decreasingStateSpectrum sigma) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P21

end
