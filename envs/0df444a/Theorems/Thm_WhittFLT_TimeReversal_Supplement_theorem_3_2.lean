-- Prove2me | Theorems.Thm_WhittFLT_TimeReversal_Supplement_theorem_3_2
-- name    : WhittFLT.TimeReversal.Supplement.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:44:24.472825+00:00
-- url     : https://prove2.me/theorems/5afbf79c-a05c-400e-9151-3d83172f6851
-- title:
--   Theorem 3.2 (companion theorem; not used in the proof of the goal) — integer-valued composition
-- statement:
--   Let $T_1,T_2,T_3$ be real intervals with $T_2\subseteq T_3$ and $S$ a complete separable metric space. Suppose $x_n,x\in F(T_3)$, so discontinuities occur only at integer times, and $y_n,y\in G(T_1,T_2)$, so the paths are nondecreasing and integer-valued. Then
--
--   $$x_n\to x\ (J_1),\quad y_n\to y\ (J_1)\quad\Longrightarrow\quad x_n\circ y_n\to x\circ y\ (J_1).$$
--
--   This is continuity of composition restricted to $F\times G$; the approximating paths must also belong to these classes.
--
--   Differences from the source:
--   - encoding: Paths and topology are described mathematically. → Use the published path predicates, intrinsic path spaces where required, and explicit interval and CSMS hypotheses.; reason: Expose the domain and conventions without presupposing any asserted theorem.
--   - encoding: Continuity in the J₁ topology. → Sequential continuity with càdlàg membership included in convergence.; reason: The path spaces are metrizable, so the sequential statement is equivalent.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), DOI 10.1287/moor.5.1.67, Theorem 3.2, p. 76 (PDF 10)

import Mathlib
import Definitions.Def_WhittFLT_TimeReversal_Supplement_Operations

namespace WhittFLT.TimeReversal.Supplement
open Set Filter Topology MeasureTheory
open WhittFLT.Composition

theorem theorem_3_2 {S : Type*} [MetricSpace S] [CompleteSpace S] [TopologicalSpace.SeparableSpace S]
    (T₁ T₂ T₃ : Set ℝ) (hT₁ : T₁.OrdConnected) (hT₂ : T₂.OrdConnected)
    (hT₃ : T₃.OrdConnected) (h₂₃ : T₂ ⊆ T₃)
    (xs : ℕ → ℝ → S) (x : ℝ → S) (ys : ℕ → ℝ → ℝ) (y : ℝ → ℝ)
    (hxs : ∀ n, InF T₃ (xs n)) (hx : InF T₃ x)
    (hys : ∀ n, InG T₁ T₂ (ys n)) (hy : InG T₁ T₂ y)
    (hxconv : J1Tendsto T₃ xs x) (hyconv : J1Tendsto T₁ ys y) :
    J1Tendsto T₁ (fun n => xs n ∘ ys n) (x ∘ y) := by sorry

end WhittFLT.TimeReversal.Supplement
