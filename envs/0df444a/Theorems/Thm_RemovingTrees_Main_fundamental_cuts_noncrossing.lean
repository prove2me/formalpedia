-- Prove2me | Theorems.Thm_RemovingTrees_Main_fundamental_cuts_noncrossing
-- name    : RemovingTrees.Main.fundamental_cuts_noncrossing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T15:21:14.117198+00:00
-- url     : https://prove2.me/theorems/24a7b3a0-012e-484a-b01d-9ec5458bf63c
-- title:
--   Claim 3.4 — Single-edge cuts of a tree do not cross
-- statement:
--   Let $T$ be a spanning tree of a finite undirected multigraph on at least two vertices. Let $S_1,S_2\subseteq V$ be shores such that
--   $$
--   |\delta_T(S_1)|=|\delta_T(S_2)|=1.
--   $$
--   Then the shores do not cross: the four sets $S_1\setminus S_2$, $S_2\setminus S_1$, $S_1\cap S_2$, and $V\setminus(S_1\cup S_2)$ cannot all be nonempty.
--
--   This is the structural input for both the warm-up laminarity result and the clique bound underlying the small-cut decomposition.
--
--   Differences from the source:
--   - encoding: finite undirected multigraphs on at least two vertices → vertices Fin n with n ≥ 2 and individually labeled edges Fin m with symmetric endpoint cuts; reason: every source graph admits such labels; loops and parallel edges are retained
-- source:
--   Nathan Klein, Neil Olver, Zi Song Yeoh, STOC 2027 submission #1092 (October 2026), Claim 3.4, p.5

import Mathlib
import Definitions.Def_RemovingTrees_Main_GraphModel

set_option autoImplicit false

namespace RemovingTrees.Main

/-- Claim 3.4, p.5; arbitrary shores, using the four-region definition of crossing. -/
theorem fundamental_cuts_noncrossing {n m : ℕ} (G : MultiGraph n m) (hn : 2 ≤ n)
    (T : Finset (Fin m)) (hT : Tree G T) (S₁ S₂ : Finset (Fin n))
    (h₁ : (cut G T S₁).card = 1) (h₂ : (cut G T S₂).card = 1) :
    ¬ Cross S₁ S₂ := by sorry
end RemovingTrees.Main
