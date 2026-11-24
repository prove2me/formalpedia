-- Prove2me | Theorems.Thm_WhittFLT_TimeReversal_Supplement_lemma_2_7
-- name    : WhittFLT.TimeReversal.Supplement.lemma_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:47:16.225658+00:00
-- url     : https://prove2.me/theorems/7c8539e8-f598-45df-9c6f-b93b5b833795
-- title:
--   Lemma 2.7 (used in the proof of Theorem 4.2) — Borel and cylinder σ-fields
-- statement:
--   Let $T$ be any real interval and $S$ a complete separable metric space. The Borel σ-field of the $J_1$ topology on $D(T,S)$ satisfies
--
--   $$\mathcal B(D(T,S),J_1)=\sigma\{\pi_t:t\in T\}.$$
--
--   The right side is defined independently as the smallest σ-field making every evaluation Borel measurable. This identifies the σ-field used by the multiplication measurability result.
--
--   Differences from the source:
--   - encoding: Paths and topology are described mathematically. → Use the published path predicates, intrinsic path spaces where required, and explicit interval and CSMS hypotheses.; reason: Expose the domain and conventions without presupposing any asserted theorem.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), DOI 10.1287/moor.5.1.67, Lemma 2.7, p. 73 (PDF 7)

import Mathlib
import Definitions.Def_WhittFLT_TimeReversal_Supplement_PathSpace

namespace WhittFLT.TimeReversal.Supplement
open Set Filter Topology MeasureTheory
open WhittFLT.Composition

theorem lemma_2_7 {S : Type*} [MetricSpace S] [CompleteSpace S] [TopologicalSpace.SeparableSpace S]
    (T : Set ℝ) (hT : T.OrdConnected) : borel (DPath T S) = cylinder T := by sorry

end WhittFLT.TimeReversal.Supplement
