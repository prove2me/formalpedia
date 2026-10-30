-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P21_qubit_tight_entropy
-- name    : QAlgorithms.Papers.Independent.Advance50.P21.qubit_tight_entropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:02:28.638712+00:00
-- url     : https://prove2.me/theorems/a23a0d5c-5abd-448a-8ffc-67308255332d
-- title:
--   Unnumbered tight qubit output entropy bound (7.8), (A.13)–(A.14)
-- statement:
--   Let $a\in[0,1]$ and fix a normalized qubit state $\sigma$. Let $\mathcal E_{a,\sigma}(\rho)=\rho\boxplus_a\sigma$ be the partial-swap channel, with $\rho\boxplus_a\sigma=a\rho+(1-a)\sigma-i\sqrt{a(1-a)}[\rho,\sigma]$. Write $H$ for von Neumann entropy in nats and $\ell(r)=h((1+r)/2)$, where $h(p)=-p\log p-(1-p)\log(1-p)$ includes continuous endpoint values. Let $\ell^{-1}:[0,\log2]\to[0,1]$ be the inverse of the decreasing nonnegative-radius branch. Then every qubit input satisfies
--   $$H(\mathcal E_{a,\sigma}(\rho))\ge\ell\bigl(a\ell^{-1}(H(\rho))+(1-a)\ell^{-1}(H(\sigma))\bigr).$$
--   For every prescribed input entropy $H_0\in[0,\log2]$, some normalized input $\rho$ with $H(\rho)=H_0$ attains equality. Aligned Bloch vectors attain the bound, with free direction when a vector vanishes. This retains the tightness of the qubit estimate.
-- source:
--   Entropy power inequalities for qudits, arXiv:1503.04213v3, PDF p. 26, Unnumbered tight qubit output entropy bound (7.8), (A.13)–(A.14)

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

/-- PDF pp.26–27, (7.8), and p.33, (A.13)–(A.14): qubit radial entropy bound and tightness.
The inverse is only on radii [0,1]. For each allowed input entropy an aligned input attains it,
including vanishing Bloch vectors and endpoint weights. -/
theorem qubit_tight_entropy (sigma : Mat 2) (hsigma : IsDensityMatrix sigma)
    (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    (∀ rho : Mat 2, IsDensityMatrix rho →
      radialEntropy (a * radialInverse (entropy rho) +
        (1 - a) * radialInverse (entropy sigma)) ≤ entropy (fixedPort a sigma rho)) ∧
    (∀ H0 ∈ Set.Icc (0 : ℝ) (Real.log 2), ∃ rho : Mat 2,
      IsDensityMatrix rho ∧ entropy rho = H0 ∧
      entropy (fixedPort a sigma rho) =
        radialEntropy (a * radialInverse H0 + (1 - a) * radialInverse (entropy sigma))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P21

end
