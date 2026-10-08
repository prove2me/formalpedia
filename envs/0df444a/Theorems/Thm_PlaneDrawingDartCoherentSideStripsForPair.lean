-- Prove2me | Theorems.Thm_PlaneDrawingDartCoherentSideStripsForPair
-- name    : PlaneDrawingDartCoherentSideStripsForPair
-- status  : Open
-- author  : @moona3k
-- created : 2026-10-04T21:40:46.091129+00:00
-- url     : https://prove2.me/theorems/6b12317b-9329-4d19-af3f-c1d067db33cc
-- title:
--   Plane Drawing Dart Coherent Side Strips For Pair
-- statement:
--   Let $G$ be a finite simple graph, $D$ a crossing-free ordinary polygonal
--   drawing, $A$ dart-arc data, and $C$ a dart vertex-sector geometry package.
--   For a dart $d$, one can choose side-strip data $S_d$ for $A.dartArc(d)$
--   and $S_{\bar d}$ for $A.dartArc(\bar d)$ such that
--   $$
--     S_d.rightStrip=S_{\bar d}.leftStrip,\qquad
--     S_{\bar d}.rightStrip=S_d.leftStrip.
--   $$
--   Both left strips are nonempty and lie in
--   $(\mathsf{OrdinaryDrawingImage}(G,D))^c$.  Near every relative-interior
--   point of either oriented arc, the drawing complement is contained in the union
--   of the two left strips.  Moreover the terminal successor sector of each of
--   $d$ and $\bar d$ meets its own left strip inside the corresponding local
--   disk, and whenever a dart $p$ has $C.star.successor(p)=d$, respectively
--   $C.star.successor(p)=\bar d$, the sector $C.successorSector(p)$ meets the
--   left strip of $d$, respectively of $\bar d$, inside the local disk at the
--   head of $p$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PlaneDrawingDartCoherentSideStripsForPair`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlaneDrawingDartCoherentSideStripsForPair.lean#L1-L835

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

lemma PlaneDrawingDartCoherentSideStripsForPair {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (A : PlaneDrawingDartArcData G D)
    (C : PlaneDrawingDartVertexSectorGeometry G D A) (d : G.Dart) :
    ∃ S : PolygonalSideStrips (A.dartArc d),
      ∃ T : PolygonalSideStrips (A.dartArc d.symm),
        S.rightStrip = T.leftStrip ∧
          T.rightStrip = S.leftStrip ∧
            S.leftStrip.Nonempty ∧
              T.leftStrip.Nonempty ∧
                S.leftStrip ⊆ (OrdinaryDrawingImage G D)ᶜ ∧
                  T.leftStrip ⊆ (OrdinaryDrawingImage G D)ᶜ ∧
                    (∀ x : EuclideanSpace ℝ (Fin 2),
                      x ∈ (A.dartArc d).relativeInterior →
                        ∃ U : Set (EuclideanSpace ℝ (Fin 2)),
                          IsOpen U ∧ x ∈ U ∧
                            U ∩ (OrdinaryDrawingImage G D)ᶜ ⊆
                              S.leftStrip ∪ T.leftStrip) ∧
                      (∀ x : EuclideanSpace ℝ (Fin 2),
                        x ∈ (A.dartArc d.symm).relativeInterior →
                          ∃ U : Set (EuclideanSpace ℝ (Fin 2)),
                            IsOpen U ∧ x ∈ U ∧
                              U ∩ (OrdinaryDrawingImage G D)ᶜ ⊆
                                T.leftStrip ∪ S.leftStrip) ∧
                        (C.successorSector d ∩ S.leftStrip ∩
                          Metric.ball (D.vertexPlacement d.toProd.2)
                            (C.star.localDiskRadius d.toProd.2)).Nonempty ∧
                          (C.successorSector d.symm ∩ T.leftStrip ∩
                            Metric.ball (D.vertexPlacement d.symm.toProd.2)
                              (C.star.localDiskRadius d.symm.toProd.2)).Nonempty ∧
                            (∀ p : G.Dart, C.star.successor p = d →
                              (C.successorSector p ∩ S.leftStrip ∩
                                Metric.ball (D.vertexPlacement p.toProd.2)
                                  (C.star.localDiskRadius p.toProd.2)).Nonempty) ∧
                              (∀ p : G.Dart, C.star.successor p = d.symm →
                                (C.successorSector p ∩ T.leftStrip ∩
                                  Metric.ball (D.vertexPlacement p.toProd.2)
                                    (C.star.localDiskRadius p.toProd.2)).Nonempty) := by sorry
