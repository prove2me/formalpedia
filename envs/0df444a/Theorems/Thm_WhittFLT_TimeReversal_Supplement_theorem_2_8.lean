-- Prove2me | Theorems.Thm_WhittFLT_TimeReversal_Supplement_theorem_2_8
-- name    : WhittFLT.TimeReversal.Supplement.theorem_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:43:34.951691+00:00
-- url     : https://prove2.me/theorems/2bbca003-9de6-497f-8d87-4397888ee3c2
-- title:
--   Theorem 2.8 (companion theorem; not used in the proof of the goal) — restriction criterion (corrected)
-- statement:
--   Let $P_n$ and $P$ be probability measures on $D(T,S)$, where $T$ is a real interval and $S$ a complete separable metric space. For a nondegenerate interval,
--
--   $$P_n\Rightarrow P\quad\Longleftrightarrow\quad\exists(s_k,t_k)_{k\ge0}:\ P_nr_{s_kt_k}^{-1}\Rightarrow Pr_{s_kt_k}^{-1}\ \text{for every }k.$$
--
--   Here $s_k$ is nonincreasing, $t_k$ is nondecreasing, $s_k<t_k$, the intervals lie in $T$ and exhaust it, and each endpoint is in $T_P$ or is an endpoint of $T$. For an empty or one-point $T$, the right side instead requires weak convergence of every evaluation law; the empty family is vacuous when $T$ is empty. This gives the full-domain restriction criterion.
--
--   **Formalization Note** As printed, an arbitrary covering sequence is insufficient: on $[0,2]$, two adjacent restrictions cannot detect alternation of the dependence between identical signed bumps on the two halves. The corrected nested exhaustion is exactly the one used in the proof (pp. 73–74). The degenerate branch avoids demanding a positive-length exhaustion of a singleton.
--
--   Differences from the source:
--   - encoding: Paths and topology are described mathematically. → Use the published path predicates, intrinsic path spaces where required, and explicit interval and CSMS hypotheses.; reason: Expose the domain and conventions without presupposing any asserted theorem.
--   - correction: An arbitrary covering sequence of compact intervals is permitted. → Use the nested continuity-endpoint exhaustion of the proof, with a coordinate-law branch for empty or one-point intervals.; reason: Adjacent intervals miss dependence across the join; positive-length exhaustions cannot cover a singleton.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), DOI 10.1287/moor.5.1.67, Theorem 2.8, p. 73 (PDF 7)

import Mathlib
import Definitions.Def_WhittFLT_TimeReversal_Supplement_PathSpace

namespace WhittFLT.TimeReversal.Supplement
open Set Filter Topology MeasureTheory
open WhittFLT.Composition

theorem theorem_2_8 {S : Type*} [MetricSpace S] [CompleteSpace S] [TopologicalSpace.SeparableSpace S]
    (T : Set ℝ) (hT : T.OrdConnected)
    (ps : ℕ → Measure (DPath T S)) (p : Measure (DPath T S))
    (hps : ∀ n, IsProbabilityMeasure (ps n)) (hp : IsProbabilityMeasure p) :
    Weakly ps p ↔
      (T.Subsingleton ∧ ∀ t : T,
        @Weakly S _ (borel S)
          (fun n => @Measure.map _ S _ (borel S) (evalD t) (ps n))
          (@Measure.map _ S _ (borel S) (evalD t) p)) ∨
      (∃ s t : ℕ → ℝ, ∃ hsub : ∀ k, Icc (s k) (t k) ⊆ T,
        Antitone s ∧ Monotone t ∧ (∀ k, s k < t k) ∧
        (∀ k, (s k ∈ TP p ∨ IsEndpoint T (s k)) ∧
          (t k ∈ TP p ∨ IsEndpoint T (t k))) ∧
        (⋃ k, Icc (s k) (t k)) = T ∧
        ∀ k, Weakly (fun n => Measure.map (restrictD (hsub k)) (ps n))
          (Measure.map (restrictD (hsub k)) p)) := by sorry

end WhittFLT.TimeReversal.Supplement
