-- Prove2me | Theorems.Thm_UnitCircleRetainedIncidenceLowerBound
-- name    : UnitCircleRetainedIncidenceLowerBound
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T18:43:16.414415+00:00
-- url     : https://prove2.me/theorems/e279228b-5fec-4037-b372-cab3843c2d95
-- title:
--   Unit Circle Retained Incidence Lower Bound
-- statement:
--   Let $P\subset\mathbb{R}^2$ be finite.  For $p\in P$, put
--   $$
--     r_p=\bigl|P\cap \operatorname{UnitCircle}(p)\bigr|
--   $$
--   where $\operatorname{UnitCircle}$ is as in `UnitCircle`, and let
--   $$
--     R=\{p\in P: r_p\ge 3\}.
--   $$
--   Then, as an inequality of real numbers,
--   $$
--     2\operatorname{unitDist}(P)-2|P|
--       \le \sum_{p\in R} r_p .
--   $$
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `UnitCircleRetainedIncidenceLowerBound`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/UnitCircleRetainedIncidenceLowerBound.lean#L1-L94

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Definitions.Def_UnitCircle
import Definitions.Def_unitDist

open Classical
open scoped BigOperators
open scoped Real
noncomputable section

lemma UnitCircleRetainedIncidenceLowerBound
    (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    2 * (unitDist P : ℝ) - 2 * (P.card : ℝ) ≤
      ∑ p ∈ P.filter
          (fun p => 3 ≤ (P.filter (fun q => q ∈ UnitCircle p)).card),
        ((P.filter (fun q => q ∈ UnitCircle p)).card : ℝ) := by sorry
