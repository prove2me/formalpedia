-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P09_example_1_4
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P09.example_1_4
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:10:31.357839+00:00
-- url     : https://prove2.me/theorems/1367e8bb-c875-4492-bfa5-4d90407d9a0b
-- title:
--   Example 1.4
-- statement:
--   Let $G$ be a group and $V$ an abelian $G$-module, and let the action of $G$ on itself be left translation. Cohomology uses the unnormalized homogeneous differential, with zero coboundaries in degree zero. For each $n\ge0$,
--
--   $$H_{\mathrm{eq}}^n(G;V)=H^n(G;V).$$
--
--   If $G$ is a topological group and $V$ a continuous abelian topological $G$-module, imposing continuity in the ordinary product topology gives $H_{\mathrm{eq},c}^n(G;V)=H_c^n(G;V)$. These equalities identify the actual cycle modulo boundary quotient groups, using the identical homogeneous complexes.
-- source:
--   A Spectral Sequence Connecting Continuous With Locally Continuous Group Cohomology, arXiv:1110.0994v1, PDF p. 3, Example 1.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P09

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P09

universe u v w

/-- PDF p. 3, Example 1.4: the identifications of Example 1.2 give the actual
homogeneous group cohomology quotients, for abstract and topological groups. -/
theorem example_1_4 :
    (∀ (G : Type u) (V : Type v) [Group G] [AddCommGroup V] [DistribMulAction G V],
      ∀ n : ℕ,
      Cohomology (equivariantCochains G (X := G) (V := V)) n =
        Cohomology (groupCochains G V) n) ∧
    (∀ (G : Type u) (V : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
      [DistribMulAction G V] [ContinuousSMul G V], ∀ n : ℕ,
      Cohomology (continuousEquivariant G (X := G) (V := V)) n =
        Cohomology (fun k => continuousCochains k ⊓ groupCochains G V k) n) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P09

end
