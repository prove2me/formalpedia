-- Prove2me | Theorems.Thm_WhittFLT_TimeReversal_Supplement_theorem_2_5
-- name    : WhittFLT.TimeReversal.Supplement.theorem_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:41:02.849824+00:00
-- url     : https://prove2.me/theorems/25199ce9-db0b-4d57-bf8a-d8ce2641873b
-- title:
--   Theorem 2.5 (companion theorem; not used in the proof of the goal) — integral J₁ metrics
-- statement:
--   Let $S$ be a complete separable metric space. The integral distances (2.2) on $D([a,\infty),S)$ and (2.3) on $D(\mathbb R,S)$ are finite metrics on paths identified on their domains. For either distance $d$, every filter $L$ and every family of càdlàg paths $x_i$ with càdlàg limit candidate $x$ satisfy
--
--   $$d(x_i,x)\to0\text{ along }L\quad\Longleftrightarrow\quad x_i\to x\text{ in extended }J_1\text{ along }L.$$
--
--   This provides metrizations compatible with the original compact-restriction definition, in both directions and for nets.
--
--   Differences from the source:
--   - encoding: Paths and topology are described mathematically. → Use the published path predicates, intrinsic path spaces where required, and explicit interval and CSMS hypotheses.; reason: Expose the domain and conventions without presupposing any asserted theorem.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), DOI 10.1287/moor.5.1.67, Theorem 2.5, p. 72 (PDF 6)

import Mathlib
import Definitions.Def_WhittFLT_TimeReversal_Supplement_IntegralMetrics

namespace WhittFLT.TimeReversal.Supplement
open Set Filter Topology MeasureTheory
open WhittFLT.Composition

theorem theorem_2_5 {S : Type*} [MetricSpace S] [CompleteSpace S] [TopologicalSpace.SeparableSpace S]
    {ι : Type*} :
    (∀ a : ℝ, IsPathMetric (Ici a) (metric22 (S := S) a)) ∧
    IsPathMetric univ (metric23 (S := S)) ∧
    (∀ (a : ℝ) (L : Filter ι) (xs : ι → ℝ → S) (x : ℝ → S),
      (∀ i, IsCadlagOn (Ici a) (xs i)) → IsCadlagOn (Ici a) x →
      (Tendsto (fun i => metric22 a (xs i) x) L (𝓝 0) ↔ J1Net (Ici a) L xs x)) ∧
    (∀ (L : Filter ι) (xs : ι → ℝ → S) (x : ℝ → S),
      (∀ i, IsCadlagOn univ (xs i)) → IsCadlagOn univ x →
      (Tendsto (fun i => metric23 (xs i) x) L (𝓝 0) ↔ J1Net univ L xs x)) := by sorry

end WhittFLT.TimeReversal.Supplement
