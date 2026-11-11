-- Prove2me | Theorems.Thm_TwoItemMenu1393_Main_lemma_B_6
-- name    : TwoItemMenu1393.Main.lemma_B_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:30:53.620431+00:00
-- url     : https://prove2.me/theorems/555e8397-f685-4211-b6c7-1066af4e2253
-- title:
--   Lemma B.6 — At most three edges per nonnull entry
-- statement:
--   Let $A_0=0$ be the null affine function, and let $A_j(v)=q_j\cdot v-p_j$ be the distinct planes of $N$ nonnull menu entries, with $q_j\in[0,1]^2$ and $p_j\ge0$. The subdivision into maximum cells with nonempty interior satisfies
--   $$\#\{\text{geometric edges}\}\le3N.$$
--   Edges are actual one-dimensional faces on the whole plane. Collinear continuations count as one unless another edge meets them. Rays and full lines are allowed; redundant or lower-dimensional entries cause no restriction. The case $N=0$ is included. This supplies the linear geometric complexity bound used with Lemma 4.3.
--
--   Differences from the source:
--   - encoding: two real coordinates → EuclideanSpace ℝ (Fin 2); reason: the coordinate isometry preserves dot products, Borel sets, Euclidean norms and all instances
--   - encoding: N distinct nonnull affine entries → a finite set S excluding null, with N=S.card; reason: sets enforce distinctness and the null entry is added once
-- source:
--   Hau Chan, Mingyu Guo, Nguyen Thach, STOC 2027 submission #1393 (October 2026), Lemma B.6, p. 19. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1393.pdf#page=19

import Definitions.Def_TwoItemMenu1393_Main_Subdivision
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Topology

namespace TwoItemMenu1393.Main

/-- Hau Chan, Mingyu Guo, Nguyen Thach, STOC 2027 submission #1393
(October 2026), Lemma B.6, p. 19.
Pinned PDF sha256: 9b1049b1045e4c9f8fe08a35eb33749c850548cb87464793e3f41f1b615fbb3e. -/
theorem lemma_B_6 (S : Finset Entry) (hS : ∀ e ∈ S, ValidEntry e)
    (hnull : nullEntry ∉ S) :
    (subdivisionEdges (insert nullEntry S)).card ≤ 3*S.card := by sorry

end TwoItemMenu1393.Main
