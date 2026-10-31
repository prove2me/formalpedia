-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P09_example_1_6
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P09.example_1_6
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:11:34.538031+00:00
-- url     : https://prove2.me/theorems/3ccbb452-1ef9-4331-88c7-9ecf185d4de9
-- title:
--   Example 1.6
-- statement:
--   Let $G$ be a topological group and $V$ an abelian topological group with a continuous $G$-action by additive automorphisms. The action on $G$ is left translation. Degree-$n$ homogeneous cochains are global functions $G^{n+1}\to V$, equivariant when $f(gx_0,\ldots,gx_n)=g\cdot f(x_0,\ldots,x_n)$. All products have their ordinary product topologies. The differential is the unnormalized alternating deletion differential, and $B^0=0$.
--
--   Let $U$ be an open identity neighborhood and $\mathcal U_U=\{gU:g\in G\}$. Then, in every degree $n\ge0$,
--
--   $$A_{cr}^n(G,\mathcal U_U;V)^G=\{f\in C_{\mathrm{hom}}^n(G;V): f|_{\mathcal U_U[n]}\text{ is continuous}\}.$$
--
--   Here $C_{\mathrm{hom}}^n$ denotes all equivariant homogeneous group cochains. Both sides carry the same alternating differential. Local continuity constrains a global function, without quotienting by equality of germs.
-- source:
--   A Spectral Sequence Connecting Continuous With Locally Continuous Group Cohomology, arXiv:1110.0994v1, PDF p. 3, Example 1.6

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P09

universe u v w

/-- PDF p. 3, Example 1.6: fixed cover-cochains are exactly homogeneous group
cochains with continuous restriction to the translated-cover neighborhood. -/
theorem example_1_6 {G : Type u} {V : Type v} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [DistribMulAction G V] [ContinuousSMul G V]
    (U : Set G) (hU : IsOpen U) (h1 : (1 : G) ∈ U)
    (C : OpenCover G) (hC : C.sets = translatedFamily U) :
    ∀ n : ℕ, (coverCochains (V := V) C n ⊓ equivariantCochains G n) =
      coverCochains C n ⊓ groupCochains G V n := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P09

end
