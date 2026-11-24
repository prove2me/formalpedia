-- Prove2me | Theorems.Thm_WhittFLT_TimeReversal_Supplement_theorem_7_5
-- name    : WhittFLT.TimeReversal.Supplement.theorem_7_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:50:37.5578+00:00
-- url     : https://prove2.me/theorems/ee696a9e-6bdd-4016-9f84-a216e868dd9f
-- title:
--   Theorem 7.5 (companion theorem; not used in the proof of the goal) — M₁ inverse FCLT
-- statement:
--   Let $x_n\in E$ and $c_n\to+\infty$. With the first-passage inverse $x_n^{-1}(t)=\inf\{s\ge0:x_n(s)>t\}$,
--
--   $$c_n(x_n-e)\to x\ (M_1')\quad\Longrightarrow\quad c_n(x_n^{-1}-e)\to-x\ (M_1').$$
--
--   This version permits jumps of either sign in the limit and does not impose $x(0)=0$.
--
--   **Formalization Note** The topology is exactly the published first-passage $M_1'$ with the completed graph extended from $0$ to $x(0)$ at the origin. The standard convention would make the printed theorem false: $x_n=e+1/c_n$ gives centered input $1$, but the centered inverse is zero at the origin and cannot converge there to $-1$ in standard $M_1$. The nonstandard origin convention is therefore explicit.
--
--   Differences from the source:
--   - encoding: Paths and topology are described mathematically. → Use the published path predicates, intrinsic path spaces where required, and explicit interval and CSMS hypotheses.; reason: Expose the domain and conventions without presupposing any asserted theorem.
--   - reading: M₁ is named without defining its origin convention. → Use the published first-passage M₁′ with x(0−)=0.; reason: The standard convention contradicts the initial value in the example xₙ=e+1/cₙ.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), DOI 10.1287/moor.5.1.67, Theorem 7.5, p. 83 (PDF 17)

import Mathlib
import Definitions.Def_WhittFLT_FirstPassage_FirstPassage
import Definitions.Def_WhittFLT_FirstPassage_M1

namespace WhittFLT.TimeReversal.Supplement
open Set Filter Topology MeasureTheory
open WhittFLT.Composition

theorem theorem_7_5 (xs : ℕ → ℝ → ℝ) (x : ℝ → ℝ) (cs : ℕ → ℝ)
    (hxs : ∀ n, WhittFLT.FirstPassage.InE (xs n)) (hc : Tendsto cs atTop atTop)
    (hconv : WhittFLT.FirstPassage.M1Tendsto (fun n t => cs n * (xs n t - t)) x) :
    WhittFLT.FirstPassage.M1Tendsto
      (fun n t => cs n * (WhittFLT.FirstPassage.firstPassage (xs n) t - t)) (fun t => -x t) := by sorry

end WhittFLT.TimeReversal.Supplement
