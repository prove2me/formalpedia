-- Prove2me | Theorems.Thm_WhittFLT_Composition_theorem_3_1_i
-- name    : WhittFLT.Composition.theorem_3_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:01:36.055828+00:00
-- url     : https://prove2.me/theorems/d5c2c601-d45e-4a24-9e68-a1fad2931a69
-- title:
--   Theorem 3.1(i) — composition at a continuous outer path
-- statement:
--   Let $T_1,T_2,T_3$ be nonempty real intervals with $T_2\subseteq T_3$ and $T_3$ not a single point, and let $S$ be a complete separable metric space. Suppose $x_n\to x$ in $D(T_3,S)$ and $y_n\to y$ in $D_0(T_1,T_2)$, where $D_0$ consists of nondecreasing càdlàg paths with values in $T_2$. If $x$ is continuous on $T_3$, then
--
--   $$
--   x_n\circ y_n\longrightarrow x\circ y\quad\text{in }D(T_1,S)\text{ under }J_1.
--   $$
--
--   This is the $C\times D_0$ case treated in part (i) of the proof of Whitt's Theorem 3.1. It captures simultaneous movement of the outer and inner paths.
--
--   **Formalization Note** The source assumes intervals and complete separability at the start of §2; these are explicit here. The nonempty $T_1$ condition records the usual meaning of “interval”; nonemptiness of $T_2,T_3$ follows from the value-range and inclusion assumptions. We also assume $T_3$ has nonempty interior: the formal $J_1$ convergence on a one-point interval imposes no condition, so for $T_3=\{0\}$, $T_1=[0,1]$, constant outer paths $x_n\equiv s_1\ne s_0\equiv x$ would otherwise satisfy every hypothesis while $x_n\circ y_n\not\to x\circ y$. The conclusion also requires each composition to be càdlàg. Continuity of the composition map is written sequentially, equivalent in these metrizable $J_1$ spaces; $J_1$ distance uses extended nonnegative values.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), Theorem 3.1, proof part (i), p. 75; https://doi.org/10.1287/moor.5.1.67

import Mathlib
import Definitions.Def_WhittFLT_Composition_SkorohodD

namespace WhittFLT.Composition

open Set Filter Topology
open scoped ENNReal

/-- Theorem 3.1, proof part (i), p. 75: the case `C × D₀`. -/
theorem theorem_3_1_i {S : Type*} [MetricSpace S] [CompleteSpace S] [TopologicalSpace.SeparableSpace S]
    (T₁ T₂ T₃ : Set ℝ) (hT₁ : T₁.OrdConnected) (hT₂ : T₂.OrdConnected)
    (hT₃ : T₃.OrdConnected) (hT₁ne : T₁.Nonempty) (hT₂₃ : T₂ ⊆ T₃)
    (hT₃nt : (interior T₃).Nonempty)
    (xs : ℕ → ℝ → S) (x : ℝ → S) (ys : ℕ → ℝ → ℝ) (y : ℝ → ℝ)
    (hys : ∀ n, MonotoneOn (ys n) T₁ ∧ MapsTo (ys n) T₁ T₂)
    (hy : MonotoneOn y T₁ ∧ MapsTo y T₁ T₂)
    (hxs : J1Tendsto T₃ xs x) (hys' : J1Tendsto T₁ ys y)
    (hx : ContinuousOn x T₃) :
    J1Tendsto T₁ (fun n => xs n ∘ ys n) (x ∘ y) := by sorry

end WhittFLT.Composition
