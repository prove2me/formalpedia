-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P26_divergence_positive
-- name    : QAlgorithms.Papers.Independent.Claimed50.P26.divergence_positive
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:01:29.293175+00:00
-- url     : https://prove2.me/theorems/0a55505a-386d-4db3-88ec-4763760bd701
-- title:
--   Lemma II.5 (positivity and equality condition)
-- statement:
--   Let $\rho$ and $\sigma$ be positive semidefinite trace-one matrices on the same nonzero finite-dimensional space, and let $\alpha>0$. Use the Petz relative Rényi entropy in bits, its Umegaki value at $\alpha=1$, the support-inclusion convention above one, and the overlap convention below one. Then
--
--   $$
--   D_\alpha(\rho\Vert\sigma)\ge0,
--   \qquad D_\alpha(\rho\Vert\sigma)=0\ \Longleftrightarrow\ \rho=\sigma.
--   $$
--
--   The divergence may be infinite. This supplies both positivity and the strict equality characterization, including singular states.
-- source:
--   A strong converse for classical channel coding using entangled inputs, arXiv:0903.2838v1, PDF p. 6, Lemma II.5 (positivity and equality condition)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P26

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate Topology

open Filter

namespace QAlgorithms.Papers.Independent.Claimed50.P26

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage depolarizing)

open QAlgorithms.Papers.Independent.Information100.P71
  (supportPower channelPower)

open QAlgorithms.Papers.Independent.Dependency50.P23
  (UACode uaCodeSuccess uaSuccess ordinaryClassicalCapacity)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Dependency50.P35 (renyiEntropy petz relative)

open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)

/-- PDF pp.6–7, Lemma II.5: all positive orders, including the Umegaki value at 1,
and singular states with correctly oriented support inclusion. -/
theorem divergence_positive {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (alpha : ℝ) (ha : 0 < alpha) (rho sigma : {rho : Matrix I I ℂ // IsDensityMatrix rho}) :
    0 ≤ petz alpha rho.1 sigma.1 ∧
      (petz alpha rho.1 sigma.1 = 0 ↔ rho.1 = sigma.1) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P26

end
