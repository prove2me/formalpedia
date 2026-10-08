-- Prove2me | Theorems.Thm_UnitCircleIncidenceDoubleCount
-- name    : UnitCircleIncidenceDoubleCount
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T18:42:19.950985+00:00
-- url     : https://prove2.me/theorems/bafd8beb-86e1-4825-b189-bb386421d4b6
-- title:
--   Unit Circle Incidence Double Count
-- statement:
--   For every finite set $P\subset\mathbb{R}^2$, the number of incidences between points of $P$ and the unit circles centered at points of $P$ is twice the number of unit distances in $P$:
--   $$
--     \operatorname{UnitCircleIncidenceCount}(P)=2\,\operatorname{unitDist}(P).
--   $$
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `UnitCircleIncidenceDoubleCount`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/UnitCircleIncidenceDoubleCount.lean#L1-L74

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Definitions.Def_UnitCircleIncidenceCount
import Definitions.Def_unitDist

open Classical
noncomputable section

lemma UnitCircleIncidenceDoubleCount (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    UnitCircleIncidenceCount P = 2 * unitDist P := by sorry
