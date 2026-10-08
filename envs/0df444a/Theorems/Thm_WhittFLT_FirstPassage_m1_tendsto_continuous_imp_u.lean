-- Prove2me | Theorems.Thm_WhittFLT_FirstPassage_m1_tendsto_continuous_imp_u
-- name    : WhittFLT.FirstPassage.m1_tendsto_continuous_imp_u
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:25:09.765144+00:00
-- url     : https://prove2.me/theorems/b6bce989-112c-4fbb-a2a5-0494bf442b52
-- title:
--   Proof of Theorem 7.2 — M₁ convergence to a continuous limit is uniform convergence on compacts
-- statement:
--   Let $x_n$, $n\ge1$, and $x$ be real-valued paths on $[0,\infty)$, with $x$ continuous on $[0,\infty)$ and $x(0)=0$. If $x_n\to x$ in $M_1$, then $x_n\to x$ uniformly on compact subintervals of $[0,\infty)$:
--   $$x_n\to x\ (M_1),\ x\in C,\ x(0)=0\quad\Longrightarrow\quad x_n\to x\ (U).$$
--
--   This is the step "Since $x^{-1}\in C$, $x_n^{-1}\to x^{-1}(U)$" of the proof of Theorem 7.2.
--
--   **Formalization Note** The hypothesis $x(0)=0$ is forced by the mission's origin convention $x(0-)=0$: a continuous $x$ with $x(0)\neq0$ has a jump at the origin in the completed graph, and $M_1$ convergence to it is not uniform near $0$ (e.g. $x\equiv1$, $x_n$ rising linearly from $0$ to $1$ on $[0,1/n]$). The path $x^{-1}$ to which the step is applied satisfies $x^{-1}(0)=0$.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), proof of Theorem 7.2, p. 82

import Mathlib
import Definitions.Def_WhittFLT_FirstPassage_M1

namespace WhittFLT.FirstPassage

open Set Filter Topology

/-- Whitt (1980), proof of Theorem 7.2, p. 82: `M₁` convergence to a continuous limit (starting at
`0`, so that the origin convention adds no jump) is uniform convergence on compacts. -/
theorem m1_tendsto_continuous_imp_u (xs : ℕ → ℝ → ℝ) (x : ℝ → ℝ)
    (h : M1Tendsto xs x) (hc : ContinuousOn x (Ici 0)) (h0 : x 0 = 0) :
    WhittFLT.Composition.UTendsto (Ici 0) xs x := by sorry

end WhittFLT.FirstPassage
