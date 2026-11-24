-- Prove2me | Theorems.Thm_WhittFLT_TimeReversal_Supplement_theorem_7_3
-- name    : WhittFLT.TimeReversal.Supplement.theorem_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:49:20.413829+00:00
-- url     : https://prove2.me/theorems/527fd1d5-c0c2-4bf2-ae77-563a39212ab8
-- title:
--   Theorem 7.3 (companion theorem; not used in the proof of the goal) — J₁ inverse FCLT
-- statement:
--   Let $x_n\in E$, so each path is càdlàg on $[0,\infty)$, unbounded above, and nonnegative at zero. Let $c_n\to+\infty$, and suppose $x(0)=0$ and $x$ has no positive jumps. Write $x_n^{-1}(t)=\inf\{s\ge0:x_n(s)>t\}$. Then
--
--   $$c_n(x_n-e)\to x\ (J_1)\quad\Longrightarrow\quad c_n(x_n^{-1}-e)\to-x\ (J_1).$$
--
--   This is Vervaat's inverse functional limit theorem with both the initial-value and jump-sign requirements retained.
--
--   Differences from the source:
--   - encoding: Paths and topology are described mathematically. → Use the published path predicates, intrinsic path spaces where required, and explicit interval and CSMS hypotheses.; reason: Expose the domain and conventions without presupposing any asserted theorem.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), DOI 10.1287/moor.5.1.67, Theorem 7.3, p. 82 (PDF 16)

import Mathlib
import Definitions.Def_WhittFLT_FirstPassage_FirstPassage

namespace WhittFLT.TimeReversal.Supplement
open Set Filter Topology MeasureTheory
open WhittFLT.Composition

theorem theorem_7_3 (xs : ℕ → ℝ → ℝ) (x : ℝ → ℝ) (cs : ℕ → ℝ)
    (hc : Tendsto cs atTop atTop) (hxs : ∀ n, WhittFLT.FirstPassage.InE (xs n))
    (hjump : WhittFLT.Reflection.NoPosJump (Ici 0) x) (hzero : x 0 = 0)
    (hconv : J1Tendsto (Ici 0) (fun n t => cs n * (xs n t - t)) x) :
    J1Tendsto (Ici 0)
      (fun n t => cs n * (WhittFLT.FirstPassage.firstPassage (xs n) t - t)) (fun t => -x t) := by sorry

end WhittFLT.TimeReversal.Supplement
