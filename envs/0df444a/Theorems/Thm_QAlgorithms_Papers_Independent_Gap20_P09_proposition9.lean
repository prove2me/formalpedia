-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P09_proposition9
-- name    : QAlgorithms.Papers.Independent.Gap20.P09.proposition9
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:26:43.677979+00:00
-- url     : https://prove2.me/theorems/d018b6ad-652c-4485-9baa-e4bd409d61c2
-- title:
--   Appendix A, Proposition 9: multipartite k-extendible states are near fully separable
-- statement:
--   All registers below have finite, strictly positive dimension. States are positive semidefinite operators of trace one, channels are completely positive and trace preserving, and marginals are partial traces of the same state. Entropies use natural logarithms, with $0\log0=0$, and $\|\cdot\|_1$ denotes the full Schatten trace norm.
--
--   Let $\rho$ be a state on $A_1\cdots A_l$, $l\ge1$, and let $K\ge1$ be an integer. Suppose $\rho$ has a normalized extension on $A_1A_{2,1}\cdots A_{2,K}\cdots A_{l,1}\cdots A_{l,K}$ which is invariant under independent permutations of the $K$ replicas of each $A_i$, $i\ge2$, and whose first-replica marginal is $\rho$. Then
--   $$\inf_{\sigma\in\operatorname{SEP}(A_1:\cdots:A_l)}\|\rho-\sigma\|_1\le\frac2K\sum_{i=2}^l(\dim A_i)^2.$$
--   The set $\operatorname{SEP}$ consists of all finite convex combinations of products of normalized local states on these same factors. No extension of $A_1$ or bosonic support condition is required.
--
--   This turns multipartite extendibility into a quantitative approximation by fully separable states. Lean indexes $K$ as $k+1$.
-- source:
--   Multipartite quantum correlations and local recoverability, arXiv:1412.0333v3, PDF p. 20, Appendix A, Proposition 9: multipartite k-extendible states are near fully separable

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P09

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology

open Filter

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

-- Exact accepted heterogeneous and selected-register bases; no local aliases.

open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis SubBasis)

open QAlgorithms.Papers.Independent.Gap48.P22
  (ReplicaBasis partyCopyMultiplicity selectedReplicaMarginal)

/-- PDF pp.20–21, Proposition 9,(A.3): mixed permutation-invariant extensions,
with A1 unreplicated and the full trace norm. k+1 is the positive extension order. -/
theorem proposition9 {m : ℕ}
    (s : QAlgorithms.Papers.Independent.Claimed50.P33.FiniteState (m+1)) (k : ℕ)
    (hext : IsMultipartiteExtendible s k) :
    fullySeparableTraceDistance s ≤ (2 / ((k : ℝ)+1)) *
      ∑ i : Fin m, (s.dims i.succ : ℝ) ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Gap20.P09

end
