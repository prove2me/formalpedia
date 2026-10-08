-- Prove2me | Theorems.Thm_PlaneDrawingDartCoherentSideStripsExist
-- name    : PlaneDrawingDartCoherentSideStripsExist
-- status  : Open
-- author  : @moona3k
-- created : 2026-10-04T21:40:42.198985+00:00
-- url     : https://prove2.me/theorems/329e7645-85a8-4e3c-bf69-e9fcf7b9892c
-- title:
--   Plane Drawing Dart Coherent Side Strips Exist
-- statement:
--   Let $G$ be a finite simple graph, let $D$ be a crossing-free ordinary
--   polygonal drawing of $G$, let $A$ be dart-arc data, and let
--   $C$ be a dart vertex-sector geometry package.  Then one can choose, for
--   each dart $d$, polygonal side-strip data $S_d$ for $A.dartArc(d)$ such
--   that:
--   $$
--     S_d.rightStrip=S_{\bar d}.leftStrip ,
--   $$
--   each exported left strip is nonempty and lies in the complement of the whole
--   drawing image, near every relative-interior point of $A.dartArc(d)$ the
--   drawing complement is contained in
--   $$
--     S_d.leftStrip\cup S_{\bar d}.leftStrip ,
--   $$
--   and for every dart $d$ the successor sector $C.successorSector(d)$ meets
--   both $S_d.leftStrip$ and
--   $S_{C.star.successor(d)}.leftStrip$ inside the local disk at the head of
--   $d$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PlaneDrawingDartCoherentSideStripsExist`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlaneDrawingDartCoherentSideStripsExist.lean#L1-L273

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Definitions.Def_OrdinaryPolygonalDrawing
import Definitions.Def_PlaneDrawingDartArcData
import Definitions.Def_PlaneDrawingDartVertexSectorGeometry
import Definitions.Def_PlaneFaceData

open Classical
noncomputable section

lemma PlaneDrawingDartCoherentSideStripsExist {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (A : PlaneDrawingDartArcData G D)
    (C : PlaneDrawingDartVertexSectorGeometry G D A) :
    ∃ sideStrips : ∀ d : G.Dart, PolygonalSideStrips (A.dartArc d),
      (∀ d : G.Dart, ((sideStrips d).leftStrip).Nonempty) ∧
        (∀ d : G.Dart, (sideStrips d).leftStrip ⊆
          (OrdinaryDrawingImage G D)ᶜ) ∧
          (∀ (d : G.Dart) (x : EuclideanSpace ℝ (Fin 2)),
            x ∈ (A.dartArc d).relativeInterior →
              ∃ U : Set (EuclideanSpace ℝ (Fin 2)),
                IsOpen U ∧ x ∈ U ∧
                  U ∩ (OrdinaryDrawingImage G D)ᶜ ⊆
                    (sideStrips d).leftStrip ∪
                      (sideStrips d.symm).leftStrip) ∧
            (∀ d : G.Dart,
              (sideStrips d).rightStrip = (sideStrips d.symm).leftStrip) ∧
              (∀ d : G.Dart,
                (C.successorSector d ∩ (sideStrips d).leftStrip ∩
                  Metric.ball (D.vertexPlacement d.toProd.2)
                    (C.star.localDiskRadius d.toProd.2)).Nonempty) ∧
                (∀ d : G.Dart,
                  (C.successorSector d ∩
                    (sideStrips (C.star.successor d)).leftStrip ∩
                      Metric.ball (D.vertexPlacement d.toProd.2)
                        (C.star.localDiskRadius d.toProd.2)).Nonempty) := by sorry
