-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P44_squeezing_in
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P44.squeezing_in
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:52:11.447499+00:00
-- url     : https://prove2.me/theorems/bd6e3e56-c100-4e52-9c81-30b229056730
-- title:
--   A compact corner-manifold closure inside a quadrant neighborhood
-- statement:
--   Let $d\ge0$ be an integer and let $\mathbb R^d_+=\{z\in\mathbb R^d:z_i\ge0\text{ for all }i\}$. Let $W$ be relatively open in this quadrant, and let $C\subseteq W$ be compact with $x\in C$. There exists a relatively open set $V$ such that
--
--   $$
--   x\in C\subseteq V\subseteq\overline V\subseteq W,
--   $$
--
--   and $\overline V$ is compact and admits a Hausdorff paracompact smooth $d$-dimensional manifold-with-corners atlas inducing its subspace topology. All closures are taken in the quadrant.
--
--   The closure is given an intrinsic manifold structure; an ambient smooth embedding is not asserted. This supplies compact corner-manifold neighborhoods used in the nested-cover construction.
-- source:
--   Equivalences of Smooth and Continuous Principal Bundles with Infinite-Dimensional Structure Group, arXiv:math/0604142v3, PDF p. 6, Lemma II.5: squeezing-in manifolds with corners

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P44

open Set

open scoped ContDiff

/-- Lemma II.5, PDF pp. 6–7: squeeze a compact subset between an open set and its
compact corner-manifold closure. All closures and open sets are relative to the
quadrant. The asserted structure is intrinsic, with the given subspace topology;
no unsupported ambient smooth-embedding conclusion is imposed. -/
theorem squeezing_in
    (d : ℕ) (w : Set (Quadrant d)) (x : Quadrant d) (c : Set (Quadrant d))
    (hw : IsOpen w) (hxc : x ∈ c) (hcw : c ⊆ w) (hc : IsCompact c) :
    ∃ v : Set (Quadrant d), IsOpen v ∧ c ⊆ v ∧ v ⊆ closure v ∧
      closure v ⊆ w ∧ IsCompact (closure v) ∧ Nonempty (CornerAtlas d (closure v)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P44

end
