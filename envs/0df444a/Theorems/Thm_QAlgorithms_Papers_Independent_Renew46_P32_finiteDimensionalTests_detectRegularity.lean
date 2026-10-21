-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P32_finiteDimensionalTests_detectRegularity
-- name    : QAlgorithms.Papers.Independent.Renew46.P32.finiteDimensionalTests_detectRegularity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:15:23.309862+00:00
-- url     : https://prove2.me/theorems/d2fe51e4-0931-420f-8d10-b7aaf7df45e3
-- title:
--   Finite-dimensional smooth tests determine differentiability
-- statement:
--   Let $K$ be $\mathbb R$ with its usual absolute value or a nontrivially valued ultrametric field. Let $E,F$ be Hausdorff topological $K$-vector spaces with $E$ metrizable, let $U\subseteq E$ be nonempty and open, and let $f:U\to F$ be any map. For every integer $k\ge0$,
--   $$f\in C^k_K(U,F)\quad\Longleftrightarrow\quad f\circ c\in C^k_K(K^{k+1},F)\text{ for every smooth }c:K^{k+1}\to U.$$
--
--   Furthermore, $f$ is smooth if and only if $f\circ c$ is smooth for every positive integer $m$ and every smooth $c:K^m\to U$. The range need not be metrizable or complete, and neither space needs to be locally convex.
-- source:
--   Differential Calculus, Manifolds and Lie Groups over Arbitrary Infinite Fields, arXiv:math/0303300v1, PDF p. 60, Theorem 12.4

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P32

namespace QAlgorithms.Papers.Independent.Renew46.P32

open Set Filter Topology

universe u v

/-- Theorem 12.4, PDF p. 60: order k is tested by dimension k+1,
including k=0; smoothness is tested in every positive finite dimension. -/
theorem finiteDimensionalTests_detectRegularity
    {K : Type} [NontriviallyNormedField K] (hK : IsRealOrUltrametric K)
    {E : Type u} [AddCommGroup E] [Module K E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul K E] [T2Space E] [TopologicalSpace.MetrizableSpace E]
    {F : Type v} [AddCommGroup F] [Module K F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul K F] [T2Space F]
    (U : Set E) (hU : IsOpen U) (hUne : U.Nonempty) (f : E → F) :
    (∀ k : ℕ, fieldCk (K := K) k U f ↔
      ∀ c : (Fin (k + 1) → K) → U,
        fieldSmooth (K := K) Set.univ (fun t => (c t : E)) →
        fieldCk (K := K) k Set.univ (fun t => f (c t))) ∧
    (fieldSmooth (K := K) U f ↔
      ∀ m : ℕ, 0 < m → ∀ c : (Fin m → K) → U,
        fieldSmooth (K := K) Set.univ (fun t => (c t : E)) →
        fieldSmooth (K := K) Set.univ (fun t => f (c t))) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P32
