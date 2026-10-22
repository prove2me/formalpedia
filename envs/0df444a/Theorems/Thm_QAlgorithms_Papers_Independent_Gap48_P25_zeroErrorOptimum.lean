-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P25_zeroErrorOptimum
-- name    : QAlgorithms.Papers.Independent.Gap48.P25.zeroErrorOptimum
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:43:21.830721+00:00
-- url     : https://prove2.me/theorems/8ddad88d-7463-49c9-bf98-967546f9e428
-- title:
--   IV.B.4: weak-laser, zero-error quadratic approximation
-- statement:
--   Write $s=tt_B\eta\in(0,1]$ for the total transmission. In the zero-error weak-pulse truncation with negligible higher photons and dark counts and perfect error correction, the normalized rate proxy is $q_s(\mu)=\mu s-\mu^2/2$ for $\mu\ge0$. It has the unique maximum
--
--   $$\mu_0=s,\qquad \max_{\mu\ge0}q_s(\mu)=s^2/2.$$
--
--   Consequently, for $s=tb$ with other transmission factors $b$ fixed, the optimized proxy equals $t^2b^2/2$. The source's photon-number approximations define this quadratic proxy; no exact Poisson optimization is asserted.
-- source:
--   The Security of Practical Quantum Key Distribution, arXiv:0802.4155v3, PDF p. 29, IV.B.4: weak-laser, zero-error quadratic approximation

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P25

open scoped BigOperators ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

/-- IV.B.4, PDF p.29: exact optimization of the zero-error weak-pulse proxy. -/
theorem zeroErrorOptimum (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) :
    zeroProxy s s = s^2/2 ∧
    (∀ mu : ℝ, 0 ≤ mu → zeroProxy s mu ≤ s^2/2) ∧
    (∀ mu : ℝ, 0 ≤ mu → (zeroProxy s mu = s^2/2 ↔ mu = s)) ∧
    (∀ t b : ℝ, (t*b)^2/2 = t^2*(b^2/2)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P25

end
