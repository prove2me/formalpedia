-- Prove2me | Theorems.Thm_WhittFLT_Composition_theorem_3_1
-- name    : WhittFLT.Composition.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:12.156792+00:00
-- url     : https://prove2.me/theorems/2ff1e338-fde0-4765-8c0c-12f0a26e55c4
-- title:
--   Theorem 3.1 — continuity of composition in the $J_1$ topology
-- statement:
--   Let $T_1,T_2,T_3$ be nonempty real intervals with $T_2\subseteq T_3$ and $T_3$ not a single point, and let $S$ be a complete separable metric space. For outer paths $x_n\to x$ in $D(T_3,S)$ and nondecreasing inner paths $y_n\to y$ in $D_0(T_1,T_2)$, assume either that $x$ is continuous on $T_3$, or that $y$ is continuous and strictly increasing on $T_1$ and $x$ is continuous at $y(t)$ for every endpoint $t$ belonging to $T_1$. Then
--
--   $$
--   x_n\circ y_n\longrightarrow x\circ y\quad\text{in }D(T_1,S)\text{ under }J_1.
--   $$
--
--   Thus the composition map is continuous at every point of $C\times D_0$ and, subject to the endpoint condition, at every point of $D\times C_0$. This is the paper's principal composition result and supports random time transformations of converging paths.
--
--   **Formalization Note** The source states continuity without an endpoint hypothesis; Bauer's Remark on p. 75 adds continuity of $x$ at $y(b)$ for a closed right endpoint $b$. We also require it at a closed left endpoint, where the printed claim otherwise has a counterexample. The assumption is only in the $D\times C_0$ case. We also assume $T_3$ has nonempty interior, since the formal $J_1$ convergence on a one-point $T_3$ imposes no condition and the $C\times D_0$ case would then fail for constant outer paths with different values. The source's interval and complete-separability conventions and membership in the càdlàg spaces are explicit. The conclusion includes càdlàg membership of the compositions. Sequential continuity is equivalent to continuity here because the path spaces are metrizable.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), Theorem 3.1 and Remark, p. 75; https://doi.org/10.1287/moor.5.1.67

import Mathlib
import Definitions.Def_WhittFLT_Composition_SkorohodD

namespace WhittFLT.Composition

open Set Filter Topology
open scoped ENNReal

/-- Theorem 3.1, p. 75, corrected at both closed endpoints of `T₁` in the `D × C₀` case. -/
theorem theorem_3_1 {S : Type*} [MetricSpace S] [CompleteSpace S] [TopologicalSpace.SeparableSpace S]
    (T₁ T₂ T₃ : Set ℝ) (hT₁ : T₁.OrdConnected) (hT₂ : T₂.OrdConnected)
    (hT₃ : T₃.OrdConnected) (hT₁ne : T₁.Nonempty) (hT₂₃ : T₂ ⊆ T₃)
    (hT₃nt : (interior T₃).Nonempty)
    (xs : ℕ → ℝ → S) (x : ℝ → S) (ys : ℕ → ℝ → ℝ) (y : ℝ → ℝ)
    (hys : ∀ n, MonotoneOn (ys n) T₁ ∧ MapsTo (ys n) T₁ T₂)
    (hy : MonotoneOn y T₁ ∧ MapsTo y T₁ T₂)
    (hxs : J1Tendsto T₃ xs x) (hys' : J1Tendsto T₁ ys y)
    (hcase : ContinuousOn x T₃ ∨
      (ContinuousOn y T₁ ∧ StrictMonoOn y T₁ ∧
        ∀ t, IsEndpoint T₁ t → ContinuousWithinAt x T₃ (y t))) :
    J1Tendsto T₁ (fun n => xs n ∘ ys n) (x ∘ y) := by sorry

end WhittFLT.Composition
