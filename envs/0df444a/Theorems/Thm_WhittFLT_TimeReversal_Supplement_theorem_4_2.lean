-- Prove2me | Theorems.Thm_WhittFLT_TimeReversal_Supplement_theorem_4_2
-- name    : WhittFLT.TimeReversal.Supplement.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:48:00.947805+00:00
-- url     : https://prove2.me/theorems/b8a13fb2-3ff4-48ed-b7e9-aa31ee06ea1d
-- title:
--   Theorem 4.2 (companion theorem; not used in the proof of the goal) — multiplication
-- statement:
--   For any real interval $T$, pointwise multiplication is a Borel measurable map
--
--   $$D(T,\mathbb R)\times D(T,\mathbb R)\longrightarrow D(T,\mathbb R),\qquad (x,y)\longmapsto xy.$$
--
--   It is $J_1$-continuous at every pair with disjoint discontinuity sets:
--
--   $$x_n\to x,\quad y_n\to y,\quad \operatorname{Disc}(x)\cap\operatorname{Disc}(y)=\varnothing\quad\Longrightarrow\quad x_ny_n\to xy.$$
--
--   The statement includes the pointwise identity of the bundled map. Both measurability for the $J_1$ Borel σ-fields and continuity are retained.
--
--   Differences from the source:
--   - encoding: Paths and topology are described mathematically. → Use the published path predicates, intrinsic path spaces where required, and explicit interval and CSMS hypotheses.; reason: Expose the domain and conventions without presupposing any asserted theorem.
--   - encoding: Continuity in the J₁ topology. → Sequential continuity with càdlàg membership included in convergence.; reason: The path spaces are metrizable, so the sequential statement is equivalent.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), DOI 10.1287/moor.5.1.67, Theorem 4.2, p. 79 (PDF 13)

import Mathlib
import Definitions.Def_WhittFLT_TimeReversal_Supplement_Operations

namespace WhittFLT.TimeReversal.Supplement
open Set Filter Topology MeasureTheory
open WhittFLT.Composition

theorem theorem_4_2 (T : Set ℝ) (hT : T.OrdConnected) :
    (∀ (p : DPath T ℝ × DPath T ℝ) (t : T),
      (multiplyD p).1 t = p.1.1 t * p.2.1 t) ∧
    Measurable (multiplyD (T := T)) ∧
    (∀ (xs ys : ℕ → ℝ → ℝ) (x y : ℝ → ℝ),
      J1Tendsto T xs x → J1Tendsto T ys y → Disjoint (disc T x) (disc T y) →
      J1Tendsto T (fun n t => xs n t * ys n t) (fun t => x t * y t)) := by sorry

end WhittFLT.TimeReversal.Supplement
