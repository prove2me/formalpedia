-- Prove2me | Theorems.Thm_PlaneTreeLeafDeletionDrawingData
-- name    : PlaneTreeLeafDeletionDrawingData
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T18:54:56.29142+00:00
-- url     : https://prove2.me/theorems/9e2a084c-e106-45bd-93d7-c90a3df4fb77
-- title:
--   Drawing data after deleting a leaf edge
-- statement:
--   Consider an ordinary polygonal drawing $D$ of a finite tree $G$ with no crossings. Given a degree-one vertex $v$, its neighbor $w$, the induced tree obtained by deleting $v$, and the corresponding edge $e=\{v,w\}$, there exists an ordinary polygonal drawing $D'$ of the induced graph with the following exact data: $D'$ is crossing-free; it preserves the old vertex placements; every remaining edge arc is inherited from a distinct old edge other than $e$; the old drawing image is the union of the new image and the carrier of $D(e)$; the placement of $w$ lies in the new image while that of $v$ does not; the induced graph has strictly fewer edges; and the endpoints of the deleted arc are the placements of $v$ and $w$ in one of the two orientations.\n\nThis is the geometric bookkeeping lemma that makes leaf deletion compatible with induction on plane-tree drawings.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlaneTreeLeafDeletionDrawingData.lean#L1-L315

import Definitions.Def_PlaneFaceData
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Copy

open Classical
noncomputable section

-- [TABLET NODE: PlaneTreeLeafDeletionDrawingData]
-- Source: https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlaneTreeLeafDeletionDrawingData.lean#L1-L315

lemma PlaneTreeLeafDeletionDrawingData {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (hTree : G.IsTree)
    {v w : V} (hvDegree : G.degree v = 1) (hvw_ne : v ≠ w) (hvw : G.Adj v w)
    (hLeaf : ∀ u : V, G.Adj v u → u = w)
    (hDeletedTree : (G.induce ({v}ᶜ : Set V)).IsTree)
    (e : G.edgeFinset) (he : e.1 = Sym2.mk v w) :
    let S : Set V := ({v}ᶜ : Set V)
    ∃ D' : OrdinaryPolygonalDrawing (G.induce S),
      D'.crossingSet.card = 0 ∧
        (∀ x : S, D'.vertexPlacement x = D.vertexPlacement x.1) ∧
          (∀ ed : (G.induce S).edgeFinset,
            ∃ eG : G.edgeFinset,
              eG.1 = Sym2.map (Subtype.val : S → V) ed.1 ∧
                eG.1 ≠ e.1 ∧
                  D'.edgeArc ed = D.edgeArc eG) ∧
            OrdinaryDrawingImage G D =
              OrdinaryDrawingImage (G.induce S) D' ∪ (D.edgeArc e).carrier ∧
            D.vertexPlacement w ∈ OrdinaryDrawingImage (G.induce S) D' ∧
            D.vertexPlacement v ∉ OrdinaryDrawingImage (G.induce S) D' ∧
            (G.induce S).edgeFinset.card < G.edgeFinset.card ∧
              (((D.edgeArc e).source = D.vertexPlacement v ∧
                  (D.edgeArc e).target = D.vertexPlacement w) ∨
                ((D.edgeArc e).source = D.vertexPlacement w ∧
                  (D.edgeArc e).target = D.vertexPlacement v)) := by sorry
