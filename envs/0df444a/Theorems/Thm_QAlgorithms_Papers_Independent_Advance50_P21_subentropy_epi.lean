-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P21_subentropy_epi
-- name    : QAlgorithms.Papers.Independent.Advance50.P21.subentropy_epi
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:51:11.109913+00:00
-- url     : https://prove2.me/theorems/c09afdf4-6c10-47a3-a2d4-9993037a1508
-- title:
--   Unnumbered subentropy EPI following Corollary 7, (3.10)
-- statement:
--   Let $d\ge1$, let $\rho,\sigma$ be positive semidefinite complex $d\times d$ matrices of trace one, and let $a\in[0,1]$. Write
--   $$
--   \rho\boxplus_a\sigma=a\rho+(1-a)\sigma-i\sqrt{a(1-a)}(\rho\sigma-\sigma\rho).
--   $$
--
--   Let $Q$ be the subentropy in nats. For distinct positive eigenvalues $\lambda_1,\ldots,\lambda_d$ it is
--   $$Q(\tau)=-\sum_{i=1}^d\frac{\lambda_i^d\log\lambda_i}{\prod_{j\ne i}(\lambda_i-\lambda_j)},$$
--   and for coincident or zero eigenvalues it is the finite continuous extension. Then
--   $$Q(\rho\boxplus_a\sigma)\ge aQ(\rho)+(1-a)Q(\sigma).$$
--   This EPI retains all density matrices, rather than restricting to simple spectra.
-- source:
--   Entropy power inequalities for qudits, arXiv:1503.04213v3, PDF p. 7, Unnumbered subentropy EPI following Corollary 7, (3.10)

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

/-- PDF pp.7–8, (3.10): subentropy EPI, with repeated and zero eigenvalues retained.
The printed n in the spectral formula means d; the accepted Haar formula supplies its limit. -/
theorem subentropy_epi {d : ℕ} (hd : 0 < d) (rho sigma : Mat d)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    a * subentropyNats rho + (1 - a) * subentropyNats sigma ≤
      subentropyNats (quditAddition a rho sigma) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P21

end
