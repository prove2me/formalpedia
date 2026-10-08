-- Prove2me | Theorems.Thm_PlaneDrawingDartGeometricClockwiseSectors
-- name    : PlaneDrawingDartGeometricClockwiseSectors
-- status  : Open
-- author  : @moona3k
-- created : 2026-10-04T21:40:47.985253+00:00
-- url     : https://prove2.me/theorems/29e826f1-ca16-41fc-9c19-9f0c731f5d9c
-- title:
--   Plane Drawing Dart Geometric Clockwise Sectors
-- statement:
--   Let $G$ be a finite simple graph, let $D$ be a crossing-free ordinary
--   polygonal drawing of $G$, and let $A$ be dart-arc data for $D$.
--   Then there exists a dart vertex-sector geometry package
--   $C$ for $G,D,A$ with the following explicit local sector model.  For
--   each dart $d=(u,v)$, let $\bar d=(v,u)$, put
--   $$
--     b_d=C.star.germDirection(v,\bar d),
--     \qquad
--     o_d=C.star.germDirection(v,C.star.successor(d)),
--   $$
--   and write $\rho_v=C.star.localDiskRadius(v)$.  If $\bar d$ is the only
--   outgoing dart at $v$, then $C.successorSector(d)$ is the slit disk
--   $$
--     B(D(v),\rho_v)\setminus
--     \bigl(\{D(v)+t b_d:t>0\}\cup\{D(v)\}\bigr).
--   $$
--   Otherwise there are real numbers $c_d,s_d$, with
--   $s_d\ne0$ or $c_d<0$, such that
--   $$
--     o_d=c_d b_d-s_d\operatorname{rot}_{90}(b_d),
--   $$
--   and, for
--   $\Phi_d(x,y)=D(v)+x b_d+y\operatorname{rot}_{90}(b_d)$,
--   $$
--    C.successorSector(d)=
--    \begin{cases}
--    \Phi_d\{(x,y):x^2+y^2<(\rho_v/\|b_d\|)^2,\ y<0,\
--      c_dy+s_dx>0\}, & s_d>0,\\
--    \Phi_d\{(x,y):x^2+y^2<(\rho_v/\|b_d\|)^2,\
--      (y<0\text{ or }c_dy+s_dx>0)\}, & s_d<0,\\
--    \Phi_d\{(x,y):x^2+y^2<(\rho_v/\|b_d\|)^2,\ y<0\}, & s_d=0.
--    \end{cases}
--   $$
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PlaneDrawingDartGeometricClockwiseSectors`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlaneDrawingDartGeometricClockwiseSectors.lean#L1-L1226

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_OrdinaryPolygonalDrawing
import Definitions.Def_PlanarRot90
import Definitions.Def_PlaneDrawingDartArcData
import Definitions.Def_PlaneDrawingDartVertexSectorGeometry

open Classical
noncomputable section

lemma PlaneDrawingDartGeometricClockwiseSectors {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (A : PlaneDrawingDartArcData G D) :
    ∃ C : PlaneDrawingDartVertexSectorGeometry G D A,
      ∀ d : G.Dart,
        let rev : {e : G.Dart // e.toProd.1 = d.toProd.2} :=
          ⟨d.symm, by simp [SimpleGraph.Dart.symm]⟩
        let nxt : {e : G.Dart // e.toProd.1 = d.toProd.2} :=
          ⟨C.star.successor d, C.star.successor_tail d⟩
        ((∀ e : {e : G.Dart // e.toProd.1 = d.toProd.2}, e = rev) ∧
          C.successorSector d =
            Metric.ball (D.vertexPlacement d.toProd.2)
                (C.star.localDiskRadius d.toProd.2) \
              ({q | ∃ t : ℝ, 0 < t ∧
                q = D.vertexPlacement d.toProd.2 +
                  t • C.star.germDirection d.toProd.2 rev} ∪
                ({D.vertexPlacement d.toProd.2} :
                  Set (EuclideanSpace ℝ (Fin 2)))))
        ∨
        (∃ c s : ℝ,
          (s ≠ 0 ∨ c < 0) ∧
          C.star.germDirection d.toProd.2 nxt =
            c • C.star.germDirection d.toProd.2 rev -
              s • PlanarRot90 (C.star.germDirection d.toProd.2 rev) ∧
          C.successorSector d =
            (let base : EuclideanSpace ℝ (Fin 2) :=
              C.star.germDirection d.toProd.2 rev
             let baseChart : EuclideanSpace ℝ (Fin 2) →
                EuclideanSpace ℝ (Fin 2) :=
              fun z => D.vertexPlacement d.toProd.2 +
                z 0 • base + z 1 • PlanarRot90 base
             if 0 < s then
               baseChart ''
                {z : EuclideanSpace ℝ (Fin 2) |
                  z 0 ^ 2 + z 1 ^ 2 <
                    (C.star.localDiskRadius d.toProd.2 / ‖base‖) ^ 2 ∧
                  z 1 < 0 ∧ 0 < c * z 1 + s * z 0}
             else if s < 0 then
               baseChart ''
                {z : EuclideanSpace ℝ (Fin 2) |
                  z 0 ^ 2 + z 1 ^ 2 <
                    (C.star.localDiskRadius d.toProd.2 / ‖base‖) ^ 2 ∧
                  (z 1 < 0 ∨ 0 < c * z 1 + s * z 0)}
             else
               baseChart ''
                {z : EuclideanSpace ℝ (Fin 2) |
                  z 0 ^ 2 + z 1 ^ 2 <
                    (C.star.localDiskRadius d.toProd.2 / ‖base‖) ^ 2 ∧
                  z 1 < 0})) := by sorry
