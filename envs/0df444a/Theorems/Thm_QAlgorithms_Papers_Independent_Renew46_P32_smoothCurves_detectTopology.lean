-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P32_smoothCurves_detectTopology
-- name    : QAlgorithms.Papers.Independent.Renew46.P32.smoothCurves_detectTopology
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:14:48.082817+00:00
-- url     : https://prove2.me/theorems/fd080ce8-b2b0-4136-9e33-8cb1ed599372
-- title:
--   Smooth curves determine the topology
-- statement:
--   Let $K$ be $\mathbb R$ with its usual absolute value or a nontrivially valued ultrametric field, let $E$ be a Hausdorff metrizable topological $K$-vector space, and let $U\subseteq E$ be nonempty and open. The topology of $U$ is final with respect to all smooth curves $c:K\to U$: a set $V\subseteq U$ is open exactly when every $c^{-1}(V)$ is open in $K$. Moreover, for every Hausdorff topological space $Z$ and map $f:U\to Z$,
--   $$f\text{ is continuous}\quad\Longleftrightarrow\quad f\circ c\text{ is continuous for every smooth }c:K\to U.$$
--
--   The target $Z$ needs no linear structure or regularity assumption.
-- source:
--   Differential Calculus, Manifolds and Lie Groups over Arbitrary Infinite Fields, arXiv:math/0303300v1, PDF p. 57, Theorem 11.3

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P32

namespace QAlgorithms.Papers.Independent.Renew46.P32

open Set Filter Topology

universe u v

/-- Theorem 11.3, PDF pp. 57--58: both the final-topology characterization
and the test for continuity into arbitrary Hausdorff topological targets. -/
theorem smoothCurves_detectTopology
    {K : Type} [NontriviallyNormedField K] (hK : IsRealOrUltrametric K)
    {E : Type u} [AddCommGroup E] [Module K E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul K E] [T2Space E] [TopologicalSpace.MetrizableSpace E]
    (U : Set E) (hU : IsOpen U) (hUne : U.Nonempty) :
    (∀ V : Set U, IsOpen V ↔
      ∀ c : K → U, fieldSmooth (K := K) Set.univ (fun t => (c t : E)) →
        IsOpen (c ⁻¹' V)) ∧
    (∀ (Z : Type v) [TopologicalSpace Z] [T2Space Z] (f : U → Z),
      Continuous f ↔ ∀ c : K → U,
        fieldSmooth (K := K) Set.univ (fun t => (c t : E)) → Continuous (f ∘ c)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P32
