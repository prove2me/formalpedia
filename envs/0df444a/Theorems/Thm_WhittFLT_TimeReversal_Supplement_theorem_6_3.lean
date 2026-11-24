-- Prove2me | Theorems.Thm_WhittFLT_TimeReversal_Supplement_theorem_6_3
-- name    : WhittFLT.TimeReversal.Supplement.theorem_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:48:34.214916+00:00
-- url     : https://prove2.me/theorems/d5f3ea1a-fc8f-4f97-9b87-0c8d79348656
-- title:
--   Theorem 6.3 (companion theorem; not used in the proof of the goal) — M₁ drift regimes
-- statement:
--   Let $T$ be a real interval with least point zero, $x_n$ real paths, and $c_n$ real numbers. Suppose $x_n-c_ne\to x$ in standard $M_1$, where $e(t)=t$ and $x^\uparrow(t)=\sup_{0\le s\le t}x(s)$. Then all three drift regimes hold:
--
--   $$c_n\to c\ \Longrightarrow\ x_n^\uparrow\to(x+ce)^\uparrow\ (M_1),$$
--   $$c_n\to+\infty\ \Longrightarrow\ x_n^\uparrow-c_ne\to x\ (M_1),$$
--   $$c_n\to-\infty\ \Longrightarrow\ x_n^\uparrow\to(t\mapsto x(0))\ (U).$$
--
--   There is no jump-sign hypothesis in the positive-drift conclusion. All three parts are posed, although the source writes out only the proof of part (ii).
--
--   **Formalization Note** Standard $M_1$ has $x(0-)=x(0)$. Using the published $M_1'$ convention would make part (iii) false: $w_n=\mathbf1_{[1/n,\infty)}\to1$ in $M_1'$, while $(w_n-n^2e)^\uparrow=0$. The domain includes bounded intervals and the one-point interval.
--
--   Differences from the source:
--   - encoding: Paths and topology are described mathematically. → Use the published path predicates, intrinsic path spaces where required, and explicit interval and CSMS hypotheses.; reason: Expose the domain and conventions without presupposing any asserted theorem.
--   - reading: M₁ is named without defining its origin convention. → Use standard M₁ with x(0−)=x(0).; reason: The M₁′ convention makes the negative-drift clause false.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), DOI 10.1287/moor.5.1.67, Theorem 6.3, p. 81 (PDF 15)

import Mathlib
import Definitions.Def_WhittFLT_TimeReversal_Supplement_StandardM1
import Definitions.Def_WhittFLT_Reflection_Supremum

namespace WhittFLT.TimeReversal.Supplement
open Set Filter Topology MeasureTheory
open WhittFLT.Composition

theorem theorem_6_3 (T : Set ℝ) (hT : T.OrdConnected) (h0 : IsLeast T 0)
    (xs : ℕ → ℝ → ℝ) (x : ℝ → ℝ) (cs : ℕ → ℝ)
    (hconv : StandardM1Tendsto T (fun n t => xs n t - cs n * t) x) :
    (∀ c : ℝ, Tendsto cs atTop (𝓝 c) →
      StandardM1Tendsto T (fun n => WhittFLT.Reflection.runSup (xs n))
        (WhittFLT.Reflection.runSup (fun t => x t + c * t))) ∧
    (Tendsto cs atTop atTop → StandardM1Tendsto T
      (fun n t => WhittFLT.Reflection.runSup (xs n) t - cs n * t) x) ∧
    (Tendsto cs atTop atBot → UTendsto T
      (fun n => WhittFLT.Reflection.runSup (xs n)) (fun _ => x 0)) := by sorry

end WhittFLT.TimeReversal.Supplement
