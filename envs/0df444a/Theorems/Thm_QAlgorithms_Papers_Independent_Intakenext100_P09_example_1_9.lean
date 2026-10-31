-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P09_example_1_9
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P09.example_1_9
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:13:25.914476+00:00
-- url     : https://prove2.me/theorems/7bba4d47-1a0a-4cc4-8622-f331d282fb6a
-- title:
--   Example 1.9
-- statement:
--   Let $G$ be a topological group and $V$ an abelian topological group with a continuous $G$-action by additive automorphisms. The action on $G$ is left translation. Degree-$n$ homogeneous cochains are global functions $G^{n+1}\to V$, equivariant when $f(gx_0,\ldots,gx_n)=g\cdot f(x_0,\ldots,x_n)$. All products have their ordinary product topologies. The differential is the unnormalized alternating deletion differential, and $B^0=0$.
--
--   For every $n\ge0$, the locally continuous fixed standard cochains are exactly
--
--   $$A_{cg}^n(G;V)^G=\{f\in C_{\mathrm{hom}}^n(G;V):\exists N\text{ open},\ \Delta\subseteq N\subseteq G^{n+1},\ f|_N\text{ continuous}\}.$$
--
--   Here $\Delta$ is the set of constant tuples and $C_{\mathrm{hom}}^n$ denotes homogeneous group cochains. This identifies the complexes with their usual homogeneous differential. The phrase continuous germ describes regularity of each global function; it does not quotient functions by germ equality.
-- source:
--   A Spectral Sequence Connecting Continuous With Locally Continuous Group Cohomology, arXiv:1110.0994v1, PDF p. 4, Example 1.9

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P09

universe u v w

/-- PDF p. 4, Example 1.9: local regularity refers to global homogeneous
cochains continuous on some open neighborhood of the whole diagonal, with
no identification of cochains having equal germs. -/
theorem example_1_9 {G : Type u} {V : Type v} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [DistribMulAction G V] [ContinuousSMul G V] :
    ∀ (n : ℕ) (f : Cochain G V n), f ∈ germEquivariant G n ↔
      (f ∈ groupCochains G V n ∧ ∃ N : Set (Fin (n + 1) → G),
        IsOpen N ∧ (∀ x : G, (fun _ => x) ∈ N) ∧ ContinuousOn f N) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P09

end
