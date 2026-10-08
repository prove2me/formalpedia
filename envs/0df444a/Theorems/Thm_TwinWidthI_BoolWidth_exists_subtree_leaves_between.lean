-- Prove2me | Theorems.Thm_TwinWidthI_BoolWidth_exists_subtree_leaves_between
-- name    : TwinWidthI.BoolWidth.exists_subtree_leaves_between
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:30:36.953913+00:00
-- url     : https://prove2.me/theorems/5d945337-3391-4db4-932e-996aaf1ea7e8
-- title:
--   Proof of Theorem 4.2, p. 3:14 — a rooted subtree with between N+1 and 2N leaves
-- statement:
--   Let $T$ be a rooted binary tree with labelled leaves (every internal node has exactly two children), and let $N\ge 1$ be an integer. If $T$ has more than $2N$ leaves, then there is an edge $e$ of $T$ such that the rooted subtree $T'$ below $e$ satisfies
--   $$N+1\ \le\ |\text{leaves}(T')|\ \le\ 2N .$$
--
--   In the proof of Theorem 4.2 (with $N=2^k$) this is the subtree found by walking down from the root into the larger child while the current subtree has more than $2^{k+1}$ leaves; the edge $e$ it hangs from gives the cut $P_e=(A_e,B_e)$ with $|A_e|\ge 2^k+1$.
--
--   **Formalization Note.** Leaves are counted with multiplicity (the length of the leaf list), which for a decomposition tree is the number of vertices of $A_e$. The edges of $T$ are its proper rooted subtrees (`properSubtrees`), so "below an edge" excludes the whole tree. The hypothesis $N\ge 1$ is needed: every tree has at least one leaf, and the conclusion is impossible for $N=0$.
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:14, proof of Theorem 4.2, "we find a rooted subtree of T with at least 2^k + 1 and at most 2^{k+1} leaves"

import Mathlib
import Definitions.Def_TwinWidthI_BoolWidth_Setting

namespace TwinWidthI.BoolWidth

open Finset

theorem exists_subtree_leaves_between {α : Type*} (T : DTree α) (N : ℕ) (hN : 1 ≤ N)
    (hT : 2 * N < T.leaves.length) :
    ∃ S ∈ T.properSubtrees, N + 1 ≤ S.leaves.length ∧ S.leaves.length ≤ 2 * N := by sorry

end TwinWidthI.BoolWidth
