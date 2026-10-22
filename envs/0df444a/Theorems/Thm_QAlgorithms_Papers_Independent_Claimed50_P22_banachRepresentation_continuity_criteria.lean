-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P22_banachRepresentation_continuity_criteria
-- name    : QAlgorithms.Papers.Independent.Claimed50.P22.banachRepresentation_continuity_criteria
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T10:09:11.323461+00:00
-- url     : https://prove2.me/theorems/6247e24f-e6d2-4e07-9a62-c2ee1bb530a2
-- title:
--   Continuity criteria for Banach representations
-- statement:
--   Let $G$ be a topological group, let $V$ be a real or complex Banach space, and let $\pi:G\to\mathrm{GL}(V)$ be a homomorphism into continuous linear automorphisms. Put $\sigma(g,v)=\pi(g)v$. The following are equivalent:
--
--   1. $\sigma$ is jointly continuous.
--   2. $\sigma$ is continuous at $(1,v)$ for every $v\in V$.
--   3. The operator norms of $\pi(g)$ are uniformly bounded on some identity neighborhood, and every orbit map $g\mapsto\pi(g)v$ is continuous.
--
--   If $G$ is metrizable, these are also equivalent to continuity of every orbit map alone. In symbols,
--
--   $$\text{(1)}\Longleftrightarrow\text{(2)}\Longleftrightarrow\text{(3)},\qquad G\text{ metrizable}\Longrightarrow[\text{(1)}\Longleftrightarrow\text{strong continuity}].$$
--
--   This separates local operator boundedness from strong continuity without imposing an operator-norm topology on the representation homomorphism.
-- source:
--   On Differentiable Vectors for Representations of Infinite Dimensional Lie Groups, arXiv:1002.1602v3, PDF p. 17, Lemma 5.2

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P22

namespace QAlgorithms.Papers.Independent.Claimed50.P22

open Set Filter Topology

universe u v w z

section BanachRepresentations

variable {K : Type u} [RCLike K]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable {V : Type w} [NormedAddCommGroup V] [NormedSpace K V]

/-- Lemma 5.2, PDF pp. 17–18: the three continuity criteria and the
additional strong-continuity equivalence when G is metrizable. -/
theorem banachRepresentation_continuity_criteria [CompleteSpace V]
    (pi : G →* (V ≃L[K] V)) :
    ((Continuous (fun p : G × V => pi p.1 p.2)) ↔
      (∀ v : V, ContinuousAt (fun p : G × V => pi p.1 p.2) (1, v))) ∧
    ((Continuous (fun p : G × V => pi p.1 p.2)) ↔
      (LocallyBoundedRepresentation pi ∧
        ∀ v : V, Continuous (fun g : G => pi g v))) ∧
    (TopologicalSpace.MetrizableSpace G →
      ((Continuous (fun p : G × V => pi p.1 p.2)) ↔
        (∀ v : V, Continuous (fun g : G => pi g v)))) := by sorry

end BanachRepresentations

end QAlgorithms.Papers.Independent.Claimed50.P22
