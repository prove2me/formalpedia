-- Prove2me | Theorems.Thm_UnitCircleCyclicAngleOrder
-- name    : UnitCircleCyclicAngleOrder
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T18:42:02.012326+00:00
-- url     : https://prove2.me/theorems/5badf857-1d71-47ea-81f7-cf2f98c3ecef
-- title:
--   Unit Circle Cyclic Angle Order
-- statement:
--   Let $p\in\mathbb R^2$, and let $S$ be a finite set with
--   $$
--     S\subseteq \operatorname{UnitCircle}(p),\qquad |S|\ge3 .
--   $$
--   Then there exists $\operatorname{UnitCircleCyclicAngleData}(p,S)$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `UnitCircleCyclicAngleOrder`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/UnitCircleCyclicAngleOrder.lean#L1-L36

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_UnitCircle
import Definitions.Def_UnitCircleCyclicAngleData

open Classical
noncomputable section

lemma UnitCircleCyclicAngleOrder
    (p : EuclideanSpace ℝ (Fin 2))
    (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (hS : (↑S : Set (EuclideanSpace ℝ (Fin 2))) ⊆ UnitCircle p)
    (hcard : 3 ≤ S.card) :
    Nonempty (UnitCircleCyclicAngleData p S) := by sorry
