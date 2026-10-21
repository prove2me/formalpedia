-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P02_fremlinRadon_decomposable
-- name    : QAlgorithms.Papers.Independent.Renew46.P02.fremlinRadon_decomposable
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T19:49:18.665375+00:00
-- url     : https://prove2.me/theorems/522be9b7-a668-490c-afc6-255861c2a170
-- title:
--   Theorem 6.5: Radon measure spaces are decomposable
-- statement:
--   Let $(X,\mathcal T,\Sigma,\mu)$ satisfy Definition 6.4: the measure is complete; its domain is locally determined by measurable finite-measure sets; $\mathcal T$ is Hausdorff and all open sets are measurable; every measurable set has measure equal to the supremum of the measures of its compact subsets; and every point has an open neighborhood of finite measure. Then there is a pairwise disjoint measurable partition $\mathcal C$ of $X$ into finite-measure sets such that
--
--   $$
--   E\in\Sigma\iff \forall K\in\mathcal C,\ E\cap K\in\Sigma,
--   \qquad
--   \mu(E)=\sum_{K\in\mathcal C}\mu(E\cap K)\quad(E\in\Sigma).
--   $$
--
--   Thus every Radon measure space in the paper's six-clause sense is decomposable, without a countability or local compactness hypothesis on the topology.
-- source:
--   Abelian von Neumann algebras, measure algebras and L^\infty-spaces, arXiv:2108.06406v2, PDF p. 28, Theorem 6.5

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P02

noncomputable section

open MeasureTheory Set

open scoped ENNReal Topology CompactlySupported

namespace QAlgorithms.Papers.Independent.Renew46.P02

universe u v

/-- Theorem 6.5, PDF p.28, with all six Radon clauses. -/
theorem fremlinRadon_decomposable {X : Type u} [TopologicalSpace X]
    [MeasurableSpace X] (mu : Measure X) (hrad : IsFremlinRadon mu) :
    IsDecomposableDomain (fun E => MeasurableSet E) (fun E => mu E) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P02

end
