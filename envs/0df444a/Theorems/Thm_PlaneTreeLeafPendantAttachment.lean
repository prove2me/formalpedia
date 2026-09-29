-- Prove2me | Theorems.Thm_PlaneTreeLeafPendantAttachment
-- name    : PlaneTreeLeafPendantAttachment
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T18:54:57.584958+00:00
-- url     : https://prove2.me/theorems/93bc9943-ec51-4a51-9395-a816ba636abd
-- title:
--   A deleted leaf arc is pendant to the remaining drawing
-- statement:
--   Let $D$ be a crossing-free ordinary polygonal drawing of a finite graph, and let $e$ be the edge incident to a deleted leaf vertex $v$. Suppose $D'$ is a compatible drawing of the induced graph on the remaining vertices, with the attachment vertex $w$ present and the deleted leaf placement absent. Then the carrier of the deleted arc meets the remaining drawing image at exactly one endpoint: either\n\n$$\n\operatorname{carrier}(D(e))\cap\operatorname{OrdinaryDrawingImage}(G\!\upharpoonright\!({\{v\}}^{\mathrm c}),D')=\{\operatorname{source}(D(e))\},\quad\operatorname{target}(D(e))\notin\operatorname{image}(D'),\n$$\n\nor the same assertion with source and target exchanged. This identifies the deleted edge as a pendant arc attached to the old drawing at $w$.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlaneTreeLeafPendantAttachment.lean#L1-L164

import Definitions.Def_PlaneFaceData

open Classical
noncomputable section

-- [TABLET NODE: PlaneTreeLeafPendantAttachment]
-- Source: https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlaneTreeLeafPendantAttachment.lean#L1-L164

lemma PlaneTreeLeafPendantAttachment {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    {v w : V} (e : G.edgeFinset) :
    let S : Set V := ({v}ᶜ : Set V)
    ∀ (D' : OrdinaryPolygonalDrawing (G.induce S)),
      (∀ x : S, D'.vertexPlacement x = D.vertexPlacement x.1) →
        (∀ ed : (G.induce S).edgeFinset,
          ∃ eG : G.edgeFinset,
            eG.1 = Sym2.map (Subtype.val : S → V) ed.1 ∧
              eG.1 ≠ e.1 ∧
                D'.edgeArc ed = D.edgeArc eG) →
          D.vertexPlacement w ∈ OrdinaryDrawingImage (G.induce S) D' →
            D.vertexPlacement v ∉ OrdinaryDrawingImage (G.induce S) D' →
              (((D.edgeArc e).source = D.vertexPlacement v ∧
                  (D.edgeArc e).target = D.vertexPlacement w) ∨
                ((D.edgeArc e).source = D.vertexPlacement w ∧
                  (D.edgeArc e).target = D.vertexPlacement v)) →
                (((D.edgeArc e).carrier ∩ OrdinaryDrawingImage (G.induce S) D' =
                    ({(D.edgeArc e).source} : Set (EuclideanSpace ℝ (Fin 2))) ∧
                    (D.edgeArc e).target ∉ OrdinaryDrawingImage (G.induce S) D') ∨
                  ((D.edgeArc e).carrier ∩ OrdinaryDrawingImage (G.induce S) D' =
                    ({(D.edgeArc e).target} : Set (EuclideanSpace ℝ (Fin 2))) ∧
                    (D.edgeArc e).source ∉ OrdinaryDrawingImage (G.induce S) D')) := by sorry
