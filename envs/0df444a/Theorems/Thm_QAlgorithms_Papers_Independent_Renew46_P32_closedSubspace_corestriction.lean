-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P32_closedSubspace_corestriction
-- name    : QAlgorithms.Papers.Independent.Renew46.P32.closedSubspace_corestriction
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:09:38.349596+00:00
-- url     : https://prove2.me/theorems/c7b086c9-bea3-47e8-9bd5-23ea177f5b60
-- title:
--   Regularity of a co-restriction to a subspace
-- statement:
--   Let $K$ be a Hausdorff nondiscrete topological field, let $E,F$ be Hausdorff topological $K$-vector spaces, let $U\subseteq E$ be open, and let $f:U\to F$ be $C^r$, where $r\in\mathbb N_0\cup\{\infty\}$. Suppose a vector subspace $F_0\subseteq F$ contains $f(U)$. If $F_0$ is closed, or if $F_0$ is sequentially closed and $K$ is metrizable, then
--   $$f:U\to F_0\quad\text{is }C^r,$$
--   where $F_0$ has the subspace topology. This permits changing the range without assuming a complement or completeness.
-- source:
--   Differential Calculus, Manifolds and Lie Groups over Arbitrary Infinite Fields, arXiv:math/0303300v1, PDF p. 48, Lemma 10.1

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P32

namespace QAlgorithms.Papers.Independent.Renew46.P32

open Set Filter Topology

universe u v

section TopologicalFieldResults

variable {K : Type} [Field K] [TopologicalSpace K]

variable [hKTop : IsTopologicalDivisionRing K] [hKT2 : T2Space K]

variable (hNonDiscrete : ¬ DiscreteTopology K)

variable {E : Type u} [AddCommGroup E] [Module K E] [TopologicalSpace E]

variable [hETop : IsTopologicalAddGroup E] [hESmul : ContinuousSMul K E] [hET2 : T2Space E]

variable {F : Type v} [AddCommGroup F] [Module K F] [TopologicalSpace F]

variable [hFTop : IsTopologicalAddGroup F] [hFSmul : ContinuousSMul K F] [hFT2 : T2Space F]

include hKTop hKT2 hNonDiscrete hETop hESmul hET2 hFTop hFSmul hFT2

/-- Lemma 10.1, PDF pp. 48--49: both closedness alternatives and every
finite order or infinity; the subspace has its induced topology. -/
theorem closedSubspace_corestriction
    (U : Set E) (hU : IsOpen U) (f : E → F) (r : WithTop ℕ)
    (hf : fieldCr (K := K) r U f) (S : Submodule K F)
    (hImage : ∀ x ∈ U, f x ∈ S)
    (hClosed : IsClosed (S : Set F) ∨
      (IsSeqClosed (S : Set F) ∧ TopologicalSpace.MetrizableSpace K)) :
    fieldCr (K := K) r U (subspaceCorestriction S U f hImage) := by sorry

end TopologicalFieldResults

end QAlgorithms.Papers.Independent.Renew46.P32
