-- Prove2me | Theorems.Thm_WhittFLT_FirstPassage_u_tendsto_imp_j1
-- name    : WhittFLT.FirstPassage.u_tendsto_imp_j1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:23:18.177581+00:00
-- url     : https://prove2.me/theorems/88d76e95-091b-400b-a413-8e82fcc5f203
-- title:
--   Proof of Theorem 7.2 — U convergence implies J₁ convergence on D([0, ∞), ℝ)
-- statement:
--   Let $x_n$, $n\ge1$, and $x$ be paths in $D([0,\infty),\mathbb R)$. If $x_n\to x$ uniformly on compact subintervals of $[0,\infty)$, then $x_n\to x$ in the $J_1$ topology:
--   $$x_n\to x\ (U)\quad\Longrightarrow\quad x_n\to x\ (J_1).$$
--
--   This is the closing step "and thus also ($J_1$)" of the proof of Theorem 7.2.
--
--   **Formalization Note** Membership of the paths in $D([0,\infty),\mathbb R)$ is a hypothesis, because the mission's $J_1$ convergence includes it.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), proof of Theorem 7.2, p. 82

import Mathlib
import Definitions.Def_WhittFLT_Composition_SkorohodD

namespace WhittFLT.FirstPassage

open Set Filter Topology

/-- Whitt (1980), proof of Theorem 7.2, p. 82: `U` convergence implies `J₁` convergence, on
`D([0, ∞), ℝ)`. -/
theorem u_tendsto_imp_j1 (xs : ℕ → ℝ → ℝ) (x : ℝ → ℝ)
    (hxs : ∀ n, WhittFLT.Composition.IsCadlagOn (Ici 0) (xs n)) (hx : WhittFLT.Composition.IsCadlagOn (Ici 0) x)
    (h : WhittFLT.Composition.UTendsto (Ici 0) xs x) : WhittFLT.Composition.J1Tendsto (Ici 0) xs x := by sorry

end WhittFLT.FirstPassage
