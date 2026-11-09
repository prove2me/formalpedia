-- Prove2me | Theorems.Thm_ThreeColorFloodIt_FixedHeight_connectivity_update_exact
-- name    : ThreeColorFloodIt.FixedHeight.connectivity_update_exact
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:33.82843+00:00
-- url     : https://prove2.me/theorems/6845507c-bbd6-4cd1-bad7-4d1fe751979b
-- title:
--   Lemma 17 — Exact two-column update and rejection tests
-- statement:
--   Let consecutive columns be $B_j,B_{j+1}$. A represented old region $R$ lies in the old prefix and every component meets $B_j$; the new vertices $U$ lie in $B_{j+1}$. Starting from the true old blocks, the explicit two-column union procedure computes exactly
--   $$\operatorname{cc}(G[R\cup U])\text{ restricted to the two-column window}.$$
--   Its rejection tests pass exactly when an active region retains a new-column representative in every component, or a retiring region is connected. An untouched stack ancestor remains connected when the full new column is added. Applying these facts to every compatible joint-node region is precisely the source's update lemma.
--
--   Differences from the source:
--   - generalization: the three-row setup in Section 4 → all positive heights and widths with full connectivity partitions; reason: Section 5.1 explicitly carries these invariants and arguments to every height; height three is an instance
--   - generalization: each node of a compatible joint template and the represented old prefix → arbitrary old and new regions satisfying the same separator and no-lost-component premises; reason: the source proof contracts old components and adds exactly the new edges independently for each region; all joint-node regions satisfy these premises
--   - encoding: finite graphs, vertices, colors and finite rooted trees → Mathlib simple graphs, finite named carriers, a shared rooted-tree model and explicit legal-sequence predicates; reason: the same source instances are represented; unused palette colors and unowned tree nodes remain allowed
-- source:
--   Zhou, Three-Color Free-Flood-It on Fixed-Height Grids Is Polynomial-Time Solvable, STOC 2027 submission #31, supplied 2026 preprint, SHA-256 222ec38f7c30952eda9e86f87b16e8d7dfc93aa0b6b9705ac931e1b56017d280, printed p. 13 (PDF 14), Lemma 17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/31.pdf

import Definitions.Def_ThreeColorFloodIt_FixedHeight_connectivity

set_option autoImplicit false

namespace ThreeColorFloodIt.FixedHeight

theorem connectivity_update_exact {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (j l : Fin n) (next : j.val + 1 = l.val)
    (R U : Set (Cell k n)) (old_prefix : R ⊆ Prefix j)
    (new_column : U ⊆ Column l) (represented : NoLost R j) :
    (∀ u v : Fin (2 * k),
      updateConnectivity (domainAt R j) (domainAt U l) (relationAt R j) u v = true ↔
        Within (Grid k n) (R ∪ U) (slotCell j l u) (slotCell j l v)) ∧
    (updatePasses (domainAt R j) (domainAt U l) (relationAt R j) ↔
      ((U.Nonempty ∧ NoLost (R ∪ U) l) ∨ (U = ∅ ∧ ConnectedSet (Grid k n) R))) ∧
    (∀ A : Set (Cell k n), ConnectedSet (Grid k n) A → Column j ⊆ A →
      ConnectedSet (Grid k n) (A ∪ Column l)) := by sorry

end ThreeColorFloodIt.FixedHeight
