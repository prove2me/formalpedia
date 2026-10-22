-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P22_continuousVectors_closed_and_continuous_action
-- name    : QAlgorithms.Papers.Independent.Claimed50.P22.continuousVectors_closed_and_continuous_action
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T10:13:00.356966+00:00
-- url     : https://prove2.me/theorems/d7dc6026-e2ce-45ac-b9e1-aea8c7eb54a9
-- title:
--   Closedness and continuity of the continuous-vector subspace
-- statement:
--   Let $G$ be a topological group and $\pi:G\to\mathrm{GL}(V)$ a locally bounded representation on a real or complex Banach space $V$. Define
--
--   $$V^0=\{v\in V:g\mapsto\pi(g)v\text{ is continuous}\}.$$
--
--   Then $V^0$ is closed and $G$-invariant. The restricted representation on $V^0$, with its subspace norm topology, is locally bounded and its action is jointly continuous. This extracts a continuous representation from a locally bounded representation whose action on all of $V$ need not be continuous.
--
--   **Formalization Note** Continuity is written with codomain $V$; invariance and the induced subtype topology make this equivalent to continuity with codomain $V^0$.
-- source:
--   On Differentiable Vectors for Representations of Infinite Dimensional Lie Groups, arXiv:1002.1602v3, PDF p. 18, Remark 5.3

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P22

namespace QAlgorithms.Papers.Independent.Claimed50.P22

open Set Filter Topology

universe u v w z

section BanachRepresentations

variable {K : Type u} [RCLike K]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable {V : Type w} [NormedAddCommGroup V] [NormedSpace K V]

/-- Remark 5.3, PDF p. 18: continuous vectors form a closed invariant
subspace with a jointly continuous, locally bounded restricted action.
Writing this action into V is equivalent to writing it into the subtype
because the latter carries the induced topology. -/
theorem continuousVectors_closed_and_continuous_action [CompleteSpace V]
    (pi : G →* (V ≃L[K] V)) (hBound : LocallyBoundedRepresentation pi) :
    IsClosed (ContinuousVectors pi) ∧
    (∀ g : G, ∀ v ∈ ContinuousVectors pi, pi g v ∈ ContinuousVectors pi) ∧
    Continuous (fun p : G × {v : V // v ∈ ContinuousVectors pi} => pi p.1 p.2.val) ∧
    (∃ U : Set G, U ∈ 𝓝 (1 : G) ∧ ∃ C : ℝ, 0 < C ∧
      ∀ g ∈ U, ∀ v ∈ ContinuousVectors pi, ‖pi g v‖ ≤ C * ‖v‖) := by sorry

end BanachRepresentations

end QAlgorithms.Papers.Independent.Claimed50.P22
