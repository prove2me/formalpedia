-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P26_optimal_ensemble_distance
-- name    : QAlgorithms.Papers.Independent.Claimed50.P26.optimal_ensemble_distance
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:05:10.894981+00:00
-- url     : https://prove2.me/theorems/5736cab7-5031-431e-b88a-fc60c3005cab
-- title:
--   Lemma II.9 (maximal distance of an optimal A-ensemble)
-- statement:
--   Let $\alpha>1$ and let $A$ be an arbitrary subset of the density matrices on a nonzero finite-dimensional space. Define $\chi_\alpha^*(A)$ as the supremum of $\chi_\alpha(E)$ over finite normalized ensembles whose component states all lie in $A$. Suppose a specified such ensemble $E^*$ attains this supremum, and let $\mu(E^*)$ be its constructed normalized Rényi center. Then
--
--   $$
--   D_\alpha(\rho_0\Vert\mu(E^*))\le\chi_\alpha^*(A)
--   \quad\text{for every }\rho_0\in A.
--   $$
--
--   Attainment is an explicit hypothesis. No closedness or convexity assumption on $A$ is added; existence of the given ensemble already implies $A\ne\varnothing$. This gives the maximal-distance property of an optimal ensemble.
-- source:
--   A strong converse for classical channel coding using entangled inputs, arXiv:0903.2838v1, PDF p. 8, Lemma II.9 (maximal distance of an optimal A-ensemble)

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

/-- PDF p.8, Lemma II.9: arbitrary subsets of density matrices; a maximizing
finite ensemble is explicitly assumed, with no added compactness/convexity. -/
theorem optimal_ensemble_distance {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (alpha : ℝ) (ha : 1 < alpha) (A : Set (Matrix I I ℂ))
    (hA : ∀ rho ∈ A, IsDensityMatrix rho) (e : Ensemble I)
    (he : ∀ x, e.state x ∈ A) (hopt : ensembleRenyiInformation alpha e = setChi alpha A) :
    ∀ rho ∈ A, petz alpha rho (ensembleRenyiCenter alpha e) ≤ (setChi alpha A : EReal) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P26

end
