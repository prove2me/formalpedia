-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P09_corollary_1_8
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P09.corollary_1_8
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:12:51.758822+00:00
-- url     : https://prove2.me/theorems/b052051d-9668-4e75-b7ef-c30021f05957
-- title:
--   Corollary 1.8
-- statement:
--   Let $G$ act continuously on a topological space $X$, with $G$ a topological group and $V$ a continuous abelian topological $G$-module. Let $H_{cg,\mathrm{eq}}^n(X;V)$ be the cohomology of global equivariant cochains continuous on a cover neighborhood of the diagonal. This is the cohomology of the complex whose degree-$n$ group is
--
--   $$\{f:X^{n+1}\to V: f\text{ is equivariant and continuous on some invariant open neighborhood of the diagonal}\}.$$
--
--   The identification is the identity on global cochains and uses the alternating homogeneous differential. It includes degree zero with $B^0=0$, and adds no nonemptiness assumption on $X$.
-- source:
--   A Spectral Sequence Connecting Continuous With Locally Continuous Group Cohomology, arXiv:1110.0994v1, PDF p. 4, Corollary 1.8

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P09

universe u v w

/-- PDF p. 4, Corollary 1.8: the locally continuous fixed complex is the
complex of equivariant cochains continuous on an invariant open diagonal
neighborhood; the second clause identifies the actual quotient cohomology. -/
theorem corollary_1_8 {G : Type w} {X : Type u} {V : Type v}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
    [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [DistribMulAction G V] [ContinuousSMul G V] :
    (∀ n : ℕ, germEquivariant G (X := X) (V := V) n =
      invariantNeighborhoodCochains G (X := X) (V := V) n) ∧
    (∀ n : ℕ, Cohomology (germEquivariant G (X := X) (V := V)) n =
      Cohomology (invariantNeighborhoodCochains G (X := X) (V := V)) n) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P09

end
