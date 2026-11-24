-- Prove2me | Theorems.Thm_WhittFLT_TimeReversal_Supplement_lemma_2_3
-- name    : WhittFLT.TimeReversal.Supplement.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:42:31.911806+00:00
-- url     : https://prove2.me/theorems/7cac4e84-45e0-4ef6-9d48-603d4f3292d1
-- title:
--   Lemma 2.3 (used in the proof of Theorem 2.8) — measurable projections and restrictions
-- statement:
--   Let $T$ be a real interval and $S$ a complete separable metric space. For $t\in T$ and $a<b$ in $T$, the maps
--
--   $$\pi_t:D(T,S)\to S,\quad \pi_t(x)=x(t),\qquad r_{ab}:D(T,S)\to D([a,b],S),\quad r_{ab}(x)=x|_{[a,b]}$$
--
--   are Borel measurable for the $J_1$ topologies. This supplies the measurable maps needed to form restricted laws.
--
--   Differences from the source:
--   - encoding: Paths and topology are described mathematically. → Use the published path predicates, intrinsic path spaces where required, and explicit interval and CSMS hypotheses.; reason: Expose the domain and conventions without presupposing any asserted theorem.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), DOI 10.1287/moor.5.1.67, Lemma 2.3, p. 71 (PDF 5)

import Mathlib
import Definitions.Def_WhittFLT_TimeReversal_Supplement_PathSpace

namespace WhittFLT.TimeReversal.Supplement
open Set Filter Topology MeasureTheory
open WhittFLT.Composition

theorem lemma_2_3 {S : Type*} [MetricSpace S] [CompleteSpace S] [TopologicalSpace.SeparableSpace S]
    (T : Set ℝ) (hT : T.OrdConnected) :
    (∀ t : T, @Measurable (DPath T S) S inferInstance (borel S) (evalD t)) ∧
    (∀ a b : ℝ, ∀ (ha : a ∈ T) (hb : b ∈ T), a < b →
      Measurable (restrictD (S := S) (hT.out ha hb))) := by sorry

end WhittFLT.TimeReversal.Supplement
