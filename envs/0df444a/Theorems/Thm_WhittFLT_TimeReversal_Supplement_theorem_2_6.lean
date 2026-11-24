-- Prove2me | Theorems.Thm_WhittFLT_TimeReversal_Supplement_theorem_2_6
-- name    : WhittFLT.TimeReversal.Supplement.theorem_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:41:39.710496+00:00
-- url     : https://prove2.me/theorems/ecd65ce2-bae6-40a5-923e-9961898aaf3f
-- title:
--   Theorem 2.6 (companion theorem; not used in the proof of the goal) — Polish path space
-- statement:
--   Let $T$ be any real interval, with endpoints finite or infinite and open or closed, and let $S$ be a complete separable metric space. Then
--
--   $$\bigl(D(T,S),J_1\bigr)\text{ is Polish}.$$
--
--   Thus the independently defined $J_1$ topology admits a complete separable compatible metric. Neither completeness of the compact distance (2.1) nor any particular complete metric is assumed. The statement includes empty and one-point intervals.
--
--   Differences from the source:
--   - encoding: Paths and topology are described mathematically. → Use the published path predicates, intrinsic path spaces where required, and explicit interval and CSMS hypotheses.; reason: Expose the domain and conventions without presupposing any asserted theorem.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), DOI 10.1287/moor.5.1.67, Theorem 2.6, p. 73 (PDF 7)

import Mathlib
import Definitions.Def_WhittFLT_TimeReversal_Supplement_PathSpace

namespace WhittFLT.TimeReversal.Supplement
open Set Filter Topology MeasureTheory
open WhittFLT.Composition

theorem theorem_2_6 {S : Type*} [MetricSpace S] [CompleteSpace S] [TopologicalSpace.SeparableSpace S]
    (T : Set ℝ) (hT : T.OrdConnected) : PolishSpace (DPath T S) := by sorry

end WhittFLT.TimeReversal.Supplement
