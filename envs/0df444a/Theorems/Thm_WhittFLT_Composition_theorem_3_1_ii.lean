-- Prove2me | Theorems.Thm_WhittFLT_Composition_theorem_3_1_ii
-- name    : WhittFLT.Composition.theorem_3_1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:35.566647+00:00
-- url     : https://prove2.me/theorems/26ade187-61f8-4e35-a25d-814cd1c0f06b
-- title:
--   Theorem 3.1(ii) — composition at a strictly increasing inner path, with endpoint correction
-- statement:
--   Let $T_1,T_2,T_3$ be nonempty real intervals with $T_2\subseteq T_3$, and let $S$ be a complete separable metric space. Suppose $x_n\to x$ in $D(T_3,S)$ and $y_n\to y$ in $D_0(T_1,T_2)$. If $y$ is continuous and strictly increasing on $T_1$, and $x$ is continuous at $y(t)$ for every endpoint $t$ belonging to $T_1$, then
--
--   $$
--   x_n\circ y_n\longrightarrow x\circ y\quad\text{in }D(T_1,S)\text{ under }J_1.
--   $$
--
--   This is the $D\times C_0$ case of Theorem 3.1 and is the part sensitive to jumps of the outer path at the image of an endpoint.
--
--   **Formalization Note** Whitt prints the theorem without the endpoint assumption; Bauer's Remark on p. 75 adds it at a closed right endpoint. We impose it at both closed endpoints because the left-endpoint case also fails without it. The assumption is vacuous at an open endpoint. All prelimit inner paths remain nondecreasing, and the conclusion includes càdlàg membership of each composition. Continuity is sequential in the metrizable $J_1$ spaces.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), Theorem 3.1, Remark and proof part (ii), p. 75; https://doi.org/10.1287/moor.5.1.67

import Mathlib
import Definitions.Def_WhittFLT_Composition_SkorohodD

namespace WhittFLT.Composition

open Set Filter Topology
open scoped ENNReal

/-- Theorem 3.1, proof part (ii), p. 75, with the endpoint correction. -/
theorem theorem_3_1_ii {S : Type*} [MetricSpace S] [CompleteSpace S] [TopologicalSpace.SeparableSpace S]
    (T₁ T₂ T₃ : Set ℝ) (hT₁ : T₁.OrdConnected) (hT₂ : T₂.OrdConnected)
    (hT₃ : T₃.OrdConnected) (hT₁ne : T₁.Nonempty) (hT₂₃ : T₂ ⊆ T₃)
    (xs : ℕ → ℝ → S) (x : ℝ → S) (ys : ℕ → ℝ → ℝ) (y : ℝ → ℝ)
    (hys : ∀ n, MonotoneOn (ys n) T₁ ∧ MapsTo (ys n) T₁ T₂)
    (hy : MonotoneOn y T₁ ∧ MapsTo y T₁ T₂)
    (hxs : J1Tendsto T₃ xs x) (hys' : J1Tendsto T₁ ys y)
    (hy₀ : ContinuousOn y T₁ ∧ StrictMonoOn y T₁)
    (hBauer : ∀ t, IsEndpoint T₁ t → ContinuousWithinAt x T₃ (y t)) :
    J1Tendsto T₁ (fun n => xs n ∘ ys n) (x ∘ y) := by sorry

end WhittFLT.Composition
