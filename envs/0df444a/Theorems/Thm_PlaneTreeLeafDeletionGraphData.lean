-- Prove2me | Theorems.Thm_PlaneTreeLeafDeletionGraphData
-- name    : PlaneTreeLeafDeletionGraphData
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T18:54:33.808125+00:00
-- url     : https://prove2.me/theorems/72b7f6e1-c55c-41e6-b00d-7584589b5a13
-- title:
--   Leaf and deletion data for a finite tree
-- statement:
--   Let $G$ be a finite simple graph with finite edge set, and suppose $G$ is a tree with at least one edge. Then there are vertices $v,w$ such that $v$ has degree one, $w$ is its unique neighbor, and deleting $v$ leaves a tree. Moreover, the edge set contains an edge represented by the unordered pair $\{v,w\}$. In symbols, the conclusion supplies\n\n$$\n\deg(v)=1,\quad v\ne w,\quad v\sim w,\quad\nG\!\upharpoonright\!({\{v\}}^{\mathrm c})\text{ is a tree},\quad\text{and}\quad \exists e\in E(G),\ e=\{v,w\}.\n$$\n\nThis packages the graph-theoretic leaf-deletion step used to induct on the number of edges in a plane-tree drawing.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlaneTreeLeafDeletionGraphData.lean#L1-L34

import Mathlib.Combinatorics.SimpleGraph.Acyclic

open Classical
noncomputable section

-- [TABLET NODE: PlaneTreeLeafDeletionGraphData]
-- Source: https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlaneTreeLeafDeletionGraphData.lean#L1-L34

lemma PlaneTreeLeafDeletionGraphData {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj]
    (hTree : G.IsTree) (hEdges : G.edgeSet ≠ ∅) :
    ∃ v w : V, G.degree v = 1 ∧ v ≠ w ∧ G.Adj v w ∧
      (∀ u : V, G.Adj v u → u = w) ∧
        (G.induce ({v}ᶜ : Set V)).IsTree ∧
          ∃ e : G.edgeFinset, e.1 = Sym2.mk v w := by sorry
