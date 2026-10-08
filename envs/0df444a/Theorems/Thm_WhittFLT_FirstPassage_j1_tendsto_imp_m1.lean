-- Prove2me | Theorems.Thm_WhittFLT_FirstPassage_j1_tendsto_imp_m1
-- name    : WhittFLT.FirstPassage.j1_tendsto_imp_m1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:25:04.675152+00:00
-- url     : https://prove2.me/theorems/52bd5f1c-f66a-418d-bc70-e30887ecfeb5
-- title:
--   §6 — the M₁ topology is weaker than the J₁ topology
-- statement:
--   Let $x_n$, $n\ge1$, and $x$ be real-valued paths on $[0,\infty)$. If $x_n\to x$ in $D([0,\infty),\mathbb R)$ with the $J_1$ topology, then $x_n\to x$ in the $M_1$ topology:
--   $$x_n\to x\ (J_1)\quad\Longrightarrow\quad x_n\to x\ (M_1).$$
--
--   This is the step of the proof of Theorem 7.2 that moves a $J_1$ hypothesis into the setting of Theorem 7.1.
--
--   **Formalization Note** The page says "The $M_1$ topology is weaker than the $J_1$ topology and coincides with the topology of pointwise convergence on the subset $D_0$ of nondecreasing real-valued functions in $D$"; this item formalizes the first clause only, sequentially and on $T=[0,\infty)$ (the setting of §§6–7). The $M_1$ topology is the one of the definition file, with the origin convention $x(0-)=0$; since $J_1$ convergence on $[0,b]$ forces $x_n(0)\to x(0)$, the convention does not affect this implication.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), §6, p. 80

import Mathlib
import Definitions.Def_WhittFLT_FirstPassage_M1

namespace WhittFLT.FirstPassage

open Set Filter Topology

/-- Whitt (1980), §6, p. 80: the `M₁` topology is weaker than the `J₁` topology (first clause), on
`D([0, ∞), ℝ)`. -/
theorem j1_tendsto_imp_m1 (xs : ℕ → ℝ → ℝ) (x : ℝ → ℝ)
    (h : WhittFLT.Composition.J1Tendsto (Ici 0) xs x) : M1Tendsto xs x := by sorry

end WhittFLT.FirstPassage
