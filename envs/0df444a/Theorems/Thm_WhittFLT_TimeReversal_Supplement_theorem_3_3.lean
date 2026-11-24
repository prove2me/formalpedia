-- Prove2me | Theorems.Thm_WhittFLT_TimeReversal_Supplement_theorem_3_3
-- name    : WhittFLT.TimeReversal.Supplement.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:46:03.844259+00:00
-- url     : https://prove2.me/theorems/b512690b-626f-4973-b7ee-9e2789d45afd
-- title:
--   Theorem 3.3 (companion theorem; not used in the proof of the goal) — recovering the outer path
-- statement:
--   Let $a\le b$ and let $x_n$ be càdlàg $S$-valued paths on $T_3$. Let $y_n:[a,b]\to T_2\subseteq T_3$ be continuous and nondecreasing, converging in $J_1$ to a continuous strictly increasing $y$. If $x_n\circ y_n\to z$ in $D([a,b],S)$, then
--
--   $$x_n\to z\circ y^{-1}\quad\text{in }D((y(a),y(b)),S).$$
--
--   If also $y_n(a)=y(a)$ and $y_n(b)=y(b)$ eventually, then
--
--   $$x_n\to z\circ y^{-1}\quad\text{in }D([y(a),y(b)],S).$$
--
--   The inverse is computed from $y$ on $[a,b]$. Both the open-image conclusion and the conditional closed-image conclusion are retained.
--
--   Differences from the source:
--   - encoding: Paths and topology are described mathematically. → Use the published path predicates, intrinsic path spaces where required, and explicit interval and CSMS hypotheses.; reason: Expose the domain and conventions without presupposing any asserted theorem.
--   - encoding: Continuity in the J₁ topology. → Sequential continuity with càdlàg membership included in convergence.; reason: The path spaces are metrizable, so the sequential statement is equivalent.
--   - generalization: A compact interval [a, b] with a < b. → a ≤ b is allowed.; reason: At a = b both conclusions hold trivially; on every a < b the statement is the source's.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), DOI 10.1287/moor.5.1.67, Theorem 3.3, p. 76 (PDF 10)

import Mathlib
import Definitions.Def_WhittFLT_TimeReversal_Supplement_Operations

namespace WhittFLT.TimeReversal.Supplement
open Set Filter Topology MeasureTheory
open WhittFLT.Composition

theorem theorem_3_3 {S : Type*} [MetricSpace S] [CompleteSpace S] [TopologicalSpace.SeparableSpace S]
    (T₂ T₃ : Set ℝ) (hT₂ : T₂.OrdConnected) (hT₃ : T₃.OrdConnected) (h₂₃ : T₂ ⊆ T₃)
    (a b : ℝ) (hab : a ≤ b) (xs : ℕ → ℝ → S) (ys : ℕ → ℝ → ℝ)
    (y : ℝ → ℝ) (z : ℝ → S)
    (hxs : ∀ n, IsCadlagOn T₃ (xs n))
    (hys : ∀ n, ContinuousOn (ys n) (Icc a b) ∧ MonotoneOn (ys n) (Icc a b) ∧
      MapsTo (ys n) (Icc a b) T₂)
    (hy : ContinuousOn y (Icc a b) ∧ StrictMonoOn y (Icc a b) ∧ MapsTo y (Icc a b) T₂)
    (hyconv : J1Tendsto (Icc a b) ys y)
    (hcomp : J1Tendsto (Icc a b) (fun n => xs n ∘ ys n) z) :
    J1Tendsto (Ioo (y a) (y b)) xs (z ∘ inverseOn (Icc a b) y) ∧
    ((∀ᶠ n in atTop, ys n a = y a ∧ ys n b = y b) →
      J1Tendsto (Icc (y a) (y b)) xs (z ∘ inverseOn (Icc a b) y)) := by sorry

end WhittFLT.TimeReversal.Supplement
