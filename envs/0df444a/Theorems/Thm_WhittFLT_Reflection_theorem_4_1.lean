-- Prove2me | Theorems.Thm_WhittFLT_Reflection_theorem_4_1
-- name    : WhittFLT.Reflection.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:56:04.282353+00:00
-- url     : https://prove2.me/theorems/304d4c2d-736e-4452-b47f-f17f9c29381c
-- title:
--   Theorem 4.1 — addition is J₁-continuous at paths with disjoint discontinuities
-- statement:
--   Let $(S,m)$ be a complete separable metric space with addition satisfying $m(s_1+s_2,s_3+s_4)\le m(s_1,s_3)+m(s_2,s_4)$. Let $T$ be a nonempty real interval. If $x_n\to x$ and $y_n\to y$ in $D(T,S)$ under $J_1$, and their limits have no common discontinuity in $T$, then
--
--   $$
--   x_n+y_n\longrightarrow x+y\quad\text{in }D(T,S)\text{ under }J_1.
--   $$
--
--   This is the continuity clause used to add a linear drift to a centered path.
--
--   **Formalization Note** The paper also asserts Borel measurability of addition; that clause is outside this mission’s topology and is omitted. The metric-space separability and completeness are explicit. Paths are total functions on $\mathbb R$, and convergence is sequential.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), Theorem 4.1, p. 79; addition assumption in §4, p. 78

import Mathlib
import Definitions.Def_WhittFLT_Composition_SkorohodD

namespace WhittFLT.Reflection

open Set Filter Topology

/-- Whitt (1980), Theorem 4.1, p. 79: the continuity clause. -/
theorem theorem_4_1 {S : Type*} [MetricSpace S] [CompleteSpace S]
    [TopologicalSpace.SeparableSpace S] [Add S]
    (hadd : ∀ s₁ s₂ s₃ s₄ : S, dist (s₁ + s₂) (s₃ + s₄) ≤ dist s₁ s₃ + dist s₂ s₄)
    (T : Set ℝ) (hT : T.OrdConnected) (hTne : T.Nonempty)
    (xs : ℕ → ℝ → S) (x : ℝ → S) (ys : ℕ → ℝ → S) (y : ℝ → S)
    (hx : WhittFLT.Composition.J1Tendsto T xs x) (hy : WhittFLT.Composition.J1Tendsto T ys y)
    (hd : WhittFLT.Composition.disc T x ∩ WhittFLT.Composition.disc T y = ∅) :
    WhittFLT.Composition.J1Tendsto T (fun n t => xs n t + ys n t) (fun t => x t + y t) := by sorry

end WhittFLT.Reflection
