-- Prove2me | Theorems.Thm_PolygonalSideStripsReverseOfSameCarrier
-- name    : PolygonalSideStripsReverseOfSameCarrier
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T21:04:52.327144+00:00
-- url     : https://prove2.me/theorems/d670979a-33c4-44e6-87d6-73be13a9f811
-- title:
--   Polygonal Side Strips Reverse Of Same Carrier
-- statement:
--   Let $\gamma$ and $\delta$ be polygonal arcs with the same carrier and
--   with source and target interchanged.  If $S$ is polygonal side-strip data
--   `PolygonalSideStrips` for $\gamma$, then there is polygonal
--   side-strip data $T$ for $\delta$ whose left strip is $S.rightStrip$ and
--   whose right strip is $S.leftStrip$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PolygonalSideStripsReverseOfSameCarrier`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalSideStripsReverseOfSameCarrier.lean#L1-L53

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Definitions.Def_PlaneFaceData
import Definitions.Def_PolygonalArc

open Classical
noncomputable section

lemma PolygonalSideStripsReverseOfSameCarrier (γ δ : PolygonalArc)
    (S : PolygonalSideStrips γ) :
    δ.carrier = γ.carrier →
      δ.source = γ.target →
        δ.target = γ.source →
          ∃ T : PolygonalSideStrips δ,
            T.leftStrip = S.rightStrip ∧ T.rightStrip = S.leftStrip := by sorry
