-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P09_corollary_3_17
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P09.corollary_3_17
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:14:26.883448+00:00
-- url     : https://prove2.me/theorems/34e38e2b-9a49-4af2-957c-85b2bae08a5f
-- title:
--   Corollary 3.17
-- statement:
--   Let $G$ be a topological group and $V$ an abelian topological group with a continuous $G$-action by additive automorphisms. The action on $G$ is left translation. Degree-$n$ homogeneous cochains are global functions $G^{n+1}\to V$, equivariant when $f(gx_0,\ldots,gx_n)=g\cdot f(x_0,\ldots,x_n)$. All products have their ordinary product topologies. The differential is the unnormalized alternating deletion differential, and $B^0=0$.
--
--   If $G$ is contractible, the inclusion of globally continuous cochains into global cochains continuous on some neighborhood of the diagonal induces, for every $n\ge0$, an isomorphism
--
--   $$H_c^n(G;V)\xrightarrow{\;\iota_*\;}H_{cg}^n(G;V).$$
--
--   The map is induced by inclusion on representatives. No contractibility or vector-space structure on $V$ is assumed.
-- source:
--   A Spectral Sequence Connecting Continuous With Locally Continuous Group Cohomology, arXiv:1110.0994v1, PDF p. 11, Corollary 3.17

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P09

universe u v w

/-- PDF p. 11, Corollary 3.17: for a contractible topological group acting on
itself by left translation, global-to-local inclusion induces an isomorphism
of cohomology groups with arbitrary continuous abelian module coefficients. -/
theorem corollary_3_17 {G : Type u} {V : Type v}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ContractibleSpace G]
    [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [DistribMulAction G V] [ContinuousSMul G V] :
    ∀ n : ℕ, Function.Bijective
      (cohomologyInclusion (continuousToGerm (G := G) (X := G) (V := V)) n) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P09

end
