-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P09_example_1_2
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P09.example_1_2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:09:57.957969+00:00
-- url     : https://prove2.me/theorems/6d459211-57fb-47a8-bb0a-62282c3cc08d
-- title:
--   Example 1.2
-- statement:
--   Let $G$ be a group and $V$ an abelian $G$-module. Write $A^n(G;V)$ for all functions $G^{n+1}\to V$, with the homogeneous alternating differential and the action $(g\cdot f)(x)=g\cdot f(g^{-1}x)$. For every $n\ge0$,
--
--   $$A^n(G;V)^G=\{f:G^{n+1}\to V\mid f(gx_0,\ldots,gx_n)=g\cdot f(x_0,\ldots,x_n)\}.$$
--
--   Thus the fixed standard complex is the homogeneous group cochain complex. If $G$ is a topological group and $V$ a continuous abelian topological $G$-module, the same identification after imposing global continuity gives the continuous homogeneous group cochain complex. The abstract clause needs no topology.
-- source:
--   A Spectral Sequence Connecting Continuous With Locally Continuous Group Cohomology, arXiv:1110.0994v1, PDF p. 2, Example 1.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P09

universe u v w

/-- PDF p. 2, Example 1.2: both abstract and continuous homogeneous group
cochains are the fixed standard cochains for the left-translation action.
The first clause has no topology hypotheses on the abstract group or module. -/
theorem example_1_2 :
    (∀ (G : Type u) (V : Type v) [Group G] [AddCommGroup V] [DistribMulAction G V],
      ∀ n : ℕ, equivariantCochains G (X := G) (V := V) n = groupCochains G V n) ∧
    (∀ (G : Type u) (V : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
      [DistribMulAction G V] [ContinuousSMul G V], ∀ n : ℕ,
      continuousEquivariant G (X := G) (V := V) n =
        continuousCochains n ⊓ groupCochains G V n) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P09

end
