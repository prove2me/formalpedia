-- Prove2me | Theorems.Thm_PolygonalArcInteriorTwoRaySectorChartTransport
-- name    : PolygonalArcInteriorTwoRaySectorChartTransport
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T18:41:34.72226+00:00
-- url     : https://prove2.me/theorems/fcf5d7fd-0bbb-4db6-be1c-2e2b449079d6
-- title:
--   Polygonal Arc Interior Two Ray Sector Chart Transport
-- statement:
--   [Transported interior two-ray sector]
--   Let $p\in\mathbb R^2$, let $\rho>0$, and let $u,v\in\mathbb R^2$ be
--   nonzero directions such that $v$ is not a positive scalar multiple of
--   $u$.  Then one can choose one of the two ordered frames $(u,v)$ or
--   $(v,u)$.  Writing the second direction in the chosen frame as
--   $$
--     \mathrm{other}=c\,\mathrm{base}+s\,\operatorname{rot}_{90}(\mathrm{base}),
--   $$
--   we have either $s>0$, or $s=0$ and $c<0$.  Put
--   $$
--     a=\rho/\|\mathrm{base}\|,\qquad
--     \Phi(x,y)=p+x\,\mathrm{base}
--         +y\,\operatorname{rot}_{90}(\mathrm{base}).
--   $$
--   Let $C=B(0,a)$, let $G_{\mathrm{base}}$ be the positive $x$-axis germ
--   inside $C$, let $G_{\mathrm{other}}$ be the positive germ in direction
--   $(c,s)$ inside $C$, and define the coordinate sectors
--   $$
--     L=\{(x,y)\in C:y>0,\ cy-sx<0\},
--     \qquad
--     R=\{(x,y)\in C:y<0\text{ or }cy-sx>0\}.
--   $$
--   Then $a>0$, $\Phi(C)=B(p,\rho)$, and $\Phi(G_{\mathrm{base}})$ and
--   $\Phi(G_{\mathrm{other}})$ are exactly the two corresponding positive
--   radial germs in $B(p,\rho)$.  Moreover $\Phi(L)$ and $\Phi(R)$ are
--   open connected disjoint subsets of the actual disk, both are disjoint from
--   the two transported germs and from $p$, and
--   $$
--     B(p,\rho)\setminus
--       \bigl(\Phi(G_{\mathrm{base}})\cup\Phi(G_{\mathrm{other}})\cup\{p\}\bigr)
--     =
--     \Phi(L)\cup\Phi(R).
--   $$
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PolygonalArcInteriorTwoRaySectorChartTransport`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcInteriorTwoRaySectorChartTransport.lean#L1-L783

import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Definitions.Def_PlanarRot90

open Set
open Classical
noncomputable section

lemma PolygonalArcInteriorTwoRaySectorChartTransport
    (p u v : EuclideanSpace ℝ (Fin 2)) (rho : ℝ)
    (hrho : 0 < rho) (hu : u ≠ 0) (hv : v ≠ 0)
    (hnot_same : ¬ ∃ t : ℝ, 0 < t ∧ v = t • u) :
    ∃ (base other : EuclideanSpace ℝ (Fin 2)) (c s : ℝ),
      ((base = u ∧ other = v) ∨ (base = v ∧ other = u)) ∧
        other = c • base + s • PlanarRot90 base ∧
        (0 < s ∨ s = 0 ∧ c < 0) ∧
        let a : ℝ := rho / ‖base‖
        let chart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
          fun z => p + z 0 • base + z 1 • PlanarRot90 base
        let C : Set (EuclideanSpace ℝ (Fin 2)) :=
          Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) a
        let Gbase : Set (EuclideanSpace ℝ (Fin 2)) :=
          {z | z ∈ C ∧ z 1 = 0 ∧ 0 < z 0}
        let Gother : Set (EuclideanSpace ℝ (Fin 2)) :=
          {z | z ∈ C ∧ ∃ t : ℝ, 0 < t ∧ z 0 = t * c ∧ z 1 = t * s}
        let L : Set (EuclideanSpace ℝ (Fin 2)) :=
          {z | z ∈ C ∧ 0 < z 1 ∧ c * z 1 - s * z 0 < 0}
        let R : Set (EuclideanSpace ℝ (Fin 2)) :=
          {z | z ∈ C ∧ (z 1 < 0 ∨ 0 < c * z 1 - s * z 0)}
        0 < a ∧
          IsOpen (chart '' C) ∧ IsOpen (chart '' L) ∧ IsOpen (chart '' R) ∧
          IsConnected (chart '' L) ∧ IsConnected (chart '' R) ∧
          Disjoint (chart '' L) (chart '' R) ∧
          chart '' C = Metric.ball p rho ∧
          chart '' Gbase =
            {q | q ∈ Metric.ball p rho ∧ ∃ t : ℝ, 0 < t ∧ q = p + t • base} ∧
          chart '' Gother =
            {q | q ∈ Metric.ball p rho ∧ ∃ t : ℝ, 0 < t ∧ q = p + t • other} ∧
          Disjoint (chart '' L)
            ((chart '' Gbase) ∪ (chart '' Gother) ∪
              ({p} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
          Disjoint (chart '' R)
            ((chart '' Gbase) ∪ (chart '' Gother) ∪
              ({p} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
          Metric.ball p rho \
              ((chart '' Gbase) ∪ (chart '' Gother) ∪
                ({p} : Set (EuclideanSpace ℝ (Fin 2)))) =
            chart '' L ∪ chart '' R := by sorry
