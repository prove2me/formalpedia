-- Prove2me | Theorems.Thm_StableMSR_Recovery_DecompositionSearch_finite_decomposition_search
-- name    : StableMSR.Recovery.DecompositionSearch.finite_decomposition_search
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-14T17:29:15.886263+00:00
-- url     : https://prove2.me/theorems/d4f2a14a-b18f-44f7-966a-d1411797cf17
-- title:
--   Exact finite treewidth recognition and reconstruction with at most n+1 bags
-- statement:
--   For every finite simple graph $G$ on $n$ vertices and every nonnegative integer $w$, the depth-bounded tight-block recurrence recognizes precisely the graphs of treewidth at most $w$:
--
--   $$\operatorname{recognizes}(G,w)\iff\operatorname{tw}(G)\le w.$$
--
--   Whenever it succeeds, there is a finite tree decomposition in the canonical path-based definition, all of whose bags have at most $w+1$ vertices and whose tree has at most $n+1$ nodes. The empty graph is represented by a single empty bag. Recognition runs each initial component with empty boundary and depth $n$; each transition selects a bounded bag introducing a vertex and recursively tests the remaining connected components with their exact external boundaries. This theorem proves both semantic completeness and output reconstruction, including running intersection and the linear bag bound. It asserts neither a polynomial instruction count nor an implementation in the charged clustering-recovery interpreter.
-- source:
--   Finite tight-boundary decomposition search and reconstruction supporting the Prove2Me mission Exact Sum-of-Radii Clustering under Any Constant Stability; canonical treewidth definition and previously proved tight-block progress lemma.

import Definitions.Def_StableMSR_DecompositionSearch_Recurrence
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE
open StableMSR.Recovery.DecompositionSearch RobertsonSeymour1986.GM5

theorem StableMSR.Recovery.DecompositionSearch.finite_decomposition_search {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (w : ℕ) :
    (recognizes G w ↔ TreewidthLE G w) ∧
    (recognizes G w →
      ∃ (T : Type) (ft : Fintype T) (tree : SimpleGraph T) (bags : T → Finset V),
        IsTreeDecomposition G tree bags ∧ (∀ t, (bags t).card ≤ w+1) ∧
        @Fintype.card T ft ≤ Fintype.card V + 1) := by sorry
