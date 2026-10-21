-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P28_lemma_1_17
-- name    : QAlgorithms.Papers.Independent.Renew46.P28.lemma_1_17
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T02:57:08.33757+00:00
-- url     : https://prove2.me/theorems/d422b176-446b-492e-a939-ff4edee84535
-- title:
--   Differentiability into projective limits
-- statement:
--   Let $\mathbb K$ be a Hausdorff nondiscrete topological field, $E$ a Hausdorff topological $\mathbb K$-vector space, and $(F_i,\phi_{ij})$ a projective system of such spaces and continuous linear bonding maps over a directed index set. Form its projective limit $F=\varprojlim_i F_i$, realized as the compatible tuples with the induced product topology, and let $\pi_i:F\to F_i$ be the limit maps. For open $U\subseteq E$, $f:U\to F$ and $k\in\mathbb N_0\cup\{\infty\}$,
--
--   $$
--   f\in C^k_{\mathbb K}\quad\Longleftrightarrow\quad
--   (\forall i)\ \pi_i\circ f\in C^k_{\mathbb K}.
--   $$
--
--   This provides the source calculus on projective limits. The directed-system convention is the one used by the source's cited Lemma 10.3 of Bertram–Glöckner–Neeb; the compatible-tuple space is constructed from the bonding maps.
-- source:
--   Lie groups over non-discrete topological fields, arXiv:math/0408008v1, PDF p. 16, Lemma 1.17

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P28

namespace QAlgorithms.Papers.Independent.Renew46.P28

open Set

open scoped TensorProduct

universe u v w

/-- Lemma 1.17, PDF p.16: regularity into the projective limit is tested by
all its canonical limit maps. The limit has the induced product topology. -/
theorem lemma_1_17
    (K : Type u) [Field K] [TopologicalSpace K] [T2Space K]
    [IsTopologicalDivisionRing K] (hK : ¬ DiscreteTopology K)
    (E : Type (max u v)) [AddCommGroup E] [Module K E] [TopologicalSpace E]
    [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul K E]
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)]
    (Fi : I → Type w) [∀ i, AddCommGroup (Fi i)] [∀ i, Module K (Fi i)]
    [∀ i, TopologicalSpace (Fi i)] [∀ i, T2Space (Fi i)]
    [∀ i, IsTopologicalAddGroup (Fi i)] [∀ i, ContinuousSMul K (Fi i)]
    (S : ProjectiveSystem K Fi)
    (U : Set E) (hU : IsOpen U) (f : U → projectiveLimit K Fi S)
    (k : WithTop ℕ) :
    bgnCr K (projectiveLimit K Fi S) k U f ↔
      ∀ i, bgnCr K (Fi i) k U (fun x => (f x).val i) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P28
