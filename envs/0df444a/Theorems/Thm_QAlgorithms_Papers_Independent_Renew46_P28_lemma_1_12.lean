-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P28_lemma_1_12
-- name    : QAlgorithms.Papers.Independent.Renew46.P28.lemma_1_12
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T02:55:40.169888+00:00
-- url     : https://prove2.me/theorems/355b78b3-cfa2-4ae0-93a2-cf5ffc253381
-- title:
--   Locality of source differentiability
-- statement:
--   Let $\mathbb K$ be a Hausdorff nondiscrete topological field, $E,F$ Hausdorff topological $\mathbb K$-vector spaces, $U\subseteq E$ open, $f:U\to F$, and $k\in\mathbb N_0\cup\{\infty\}$. If $(U_i)_{i\in I}$ is an arbitrary open cover of $U$ and every restriction is $C^k_{\mathbb K}$, then
--
--   $$
--   f\in C^k_{\mathbb K}(U,F).
--   $$
--
--   Here differentiability is defined using continuous extended difference quotients, and infinite order means every finite order. This is the locality principle for that calculus. Neither the domain nor the cover is required to be nonempty.
-- source:
--   Lie groups over non-discrete topological fields, arXiv:math/0408008v1, PDF p. 15, Lemma 1.12

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P28

namespace QAlgorithms.Papers.Independent.Renew46.P28

open Set

open scoped TensorProduct

universe u v w

/-- Lemma 1.12, PDF pp.15–16: source C^k regularity is local on an arbitrary
open cover. The cover and the domain may be empty. -/
theorem lemma_1_12
    (K : Type u) [Field K] [TopologicalSpace K] [T2Space K]
    [IsTopologicalDivisionRing K] (hK : ¬ DiscreteTopology K)
    (E : Type (max u v)) [AddCommGroup E] [Module K E] [TopologicalSpace E]
    [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul K E]
    (F : Type w) [AddCommGroup F] [Module K F] [TopologicalSpace F]
    [T2Space F] [IsTopologicalAddGroup F] [ContinuousSMul K F]
    (U : Set E) (hU : IsOpen U) (f : U → F) (k : WithTop ℕ)
    {I : Type*} (Ui : I → Set E) (hUi : ∀ i, IsOpen (Ui i))
    (hsub : ∀ i, Ui i ⊆ U) (hcover : U = ⋃ i, Ui i)
    (hlocal : ∀ i, bgnCr K F k (Ui i) (fun x => f ⟨x.val, hsub i x.property⟩)) :
    bgnCr K F k U f := by sorry

end QAlgorithms.Papers.Independent.Renew46.P28
