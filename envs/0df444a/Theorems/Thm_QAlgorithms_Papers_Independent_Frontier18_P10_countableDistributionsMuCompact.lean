-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P10_countableDistributionsMuCompact
-- name    : QAlgorithms.Papers.Independent.Frontier18.P10.countableDistributionsMuCompact
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:13:28.079483+00:00
-- url     : https://prove2.me/theorems/2f9e8236-2a4e-44e5-8446-8e2bc7ba750e
-- title:
--   Corollary 3: countable probability distributions
-- statement:
--   The set of countable probability distributions, viewed in $\ell^1(\mathbb N)$ with its norm topology, is $\mu$-compact:
--   $$\mathcal P_{\mathbb N}=\{x:x_i\ge0,\ \sum_i x_i=1\}.$$
--
--
--   Normalization distinguishes this domain from the subprobability simplexes.
-- source:
--   Generalized compactness in linear spaces and its applications, arXiv:1002.3610v3, PDF p. 10, Corollary 3: countable probability distributions

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P10

noncomputable section

open Set Filter MeasureTheory TopologicalSpace

open scoped Topology ENNReal BigOperators

universe u v w

namespace QAlgorithms.Papers.Independent.Frontier18.P10

open QAlgorithms.Papers.Independent.Dependency50.P25

attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperBorel

section LpResults

/-- Corollary 3, PDF p.10: countably many outcomes, l^1 topology, total mass one. -/
theorem countableDistributionsMuCompact : MuCompact countableProbabilitySimplex := by sorry

end LpResults

end QAlgorithms.Papers.Independent.Frontier18.P10

end
