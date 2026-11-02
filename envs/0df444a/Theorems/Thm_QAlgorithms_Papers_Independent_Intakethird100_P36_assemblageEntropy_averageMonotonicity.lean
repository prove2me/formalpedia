-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P36_assemblageEntropy_averageMonotonicity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P36.assemblageEntropy_averageMonotonicity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:24:51.387138+00:00
-- url     : https://prove2.me/theorems/f273eef5-3873-44ab-bea6-20fe49bbd13b
-- title:
--   Assemblage relative entropy does not increase on average
-- statement:
--   Let \(\rho,\sigma\) be normalized finite-dimensional no-signaling assemblages with identical alphabets and Bob space, and let \(\{M_w\}\) be the same complete Bob-to-Alice 1W-LOCC instrument applied to both. Write \(p_w=\operatorname{Tr}M_w(\rho)\) and \(q_w=\operatorname{Tr}M_w(\sigma)\). For the assemblage relative entropy \(S_A\) of (18),
--
--   $$
--   \sum_wp_w S_A\!\left(\frac{M_w(\rho)}{p_w}\,\middle\|\,\frac{M_w(\sigma)}{q_w}\right)
--   \le S_A(\rho\|\sigma).
--   $$
--
--   A summand is zero for \(p_w=0\), and is \(+\infty\) for \(p_w>0=q_w\). The quantities are extended nonnegative reals, and no support-inclusion assumption is imposed. This conditional average contraction is the distinguishability result used to obtain steering monotonicity.
-- source:
--   The resource theory of steering, arXiv:1409.5804v3, PDF p. 11, Appendix C, Lemma 1, (C1)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P36

noncomputable section

open scoped BigOperators ENNReal ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P36

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable

variable {d r s df rf sf m : ℕ}

/-- Appendix C, Lemma 1, PDF p.11, (C1); proof pp.16–18. The two denominators
and the averaging law are kept distinct, with homogeneous zero-assemblageMass handling. -/
theorem assemblageEntropy_averageMonotonicity (P : SteeringProtocol d r s df rf sf m)
    (hcomplete : P.Complete) (rho sigma : AssemblageBlocks d r s)
    (hrho : IsNormalized rho) (hsigma : IsNormalized sigma) :
    ∑ w, entropyBranch P rho sigma w ≤ assemblageEntropy rho sigma := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P36

end
