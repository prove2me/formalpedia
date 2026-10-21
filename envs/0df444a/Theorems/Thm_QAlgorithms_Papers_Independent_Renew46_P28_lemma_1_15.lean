-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P28_lemma_1_15
-- name    : QAlgorithms.Papers.Independent.Renew46.P28.lemma_1_15
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T02:56:16.895867+00:00
-- url     : https://prove2.me/theorems/bc9e7984-acde-49bf-b763-1c75d48550f1
-- title:
--   Corestriction to closed or sequentially closed vector subspaces
-- statement:
--   Let $\mathbb K$ be a Hausdorff nondiscrete topological field, $E,F$ Hausdorff topological $\mathbb K$-vector spaces, $U\subseteq E$ open, and $f:U\to F$ be $C^k_{\mathbb K}$, where $k\in\mathbb N_0\cup\{\infty\}$. Let $F_0\subseteq F$ be a vector subspace containing $f(U)$, with the induced topology. If $F_0$ is closed, or if $F_0$ is sequentially closed and $\mathbb K$ is metrizable, then
--
--   $$
--   f:U\longrightarrow F_0\quad\text{is }C^k_{\mathbb K}.
--   $$
--
--   This permits changes of codomain to the indicated subspaces while retaining the source's differentiability order. No completeness or normability is assumed.
-- source:
--   Lie groups over non-discrete topological fields, arXiv:math/0408008v1, PDF p. 16, Lemma 1.15

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P28

namespace QAlgorithms.Papers.Independent.Renew46.P28

open Set

open scoped TensorProduct

universe u v w

/-- Lemma 1.15, PDF p.16: corestriction to a closed subspace, or to a
sequentially closed subspace when the scalar field is metrizable. The subspace
carries precisely the induced topology. -/
theorem lemma_1_15
    (K : Type u) [Field K] [TopologicalSpace K] [T2Space K]
    [IsTopologicalDivisionRing K] (hK : ¬ DiscreteTopology K)
    (E : Type (max u v)) [AddCommGroup E] [Module K E] [TopologicalSpace E]
    [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul K E]
    (F : Type w) [AddCommGroup F] [Module K F] [TopologicalSpace F]
    [T2Space F] [IsTopologicalAddGroup F] [ContinuousSMul K F]
    (U : Set E) (hU : IsOpen U) (f : U → F) (k : WithTop ℕ)
    (hf : bgnCr K F k U f) (F0 : Submodule K F)
    (himage : ∀ x, f x ∈ F0)
    (hclosed : IsClosed (F0 : Set F) ∨
      (IsSeqClosed (F0 : Set F) ∧ TopologicalSpace.MetrizableSpace K)) :
    bgnCr K F0 k U (fun x => ⟨f x, himage x⟩) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P28
