-- Prove2me | Theorems.Thm_WhittFLT_FirstPassage_theorem_7_2
-- name    : WhittFLT.FirstPassage.theorem_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:25:06.036609+00:00
-- url     : https://prove2.me/theorems/5364df0b-5e4c-438e-b8c1-f372d856b5ce
-- title:
--   Theorem 7.2 (continuity) — the first passage time function is J₁-continuous at each strictly increasing x
-- statement:
--   Let $E$ be the set of paths $x\in D([0,\infty),\mathbb R)$ that are unbounded above and have $x(0)\ge0$, and for $x\in E$ let $x^{-1}(t)=\inf\{s\ge0:x(s)>t\}$ be its first passage time function. Let $x_n$, $n\ge1$, and $x$ be elements of $E$ with $x$ strictly increasing on $[0,\infty)$. If $x_n\to x$ in the $J_1$ topology, then
--   $$x_n^{-1}\to x^{-1}\quad (J_1).$$
--
--   The first passage time map is not $J_1$-continuous on all of $E$ (the paper gives a counterexample on p. 82); this theorem identifies the strictly increasing paths as points of continuity. Through the continuous mapping theorem it turns a functional limit theorem for a cumulative process with strictly increasing limit (e.g. a renewal-type process with drift) into one for its first passage times.
--
--   **Formalization Note** The page states "The first passage time function mapping $E(J_1)$ into $E\cap D_0(J_1)$ is measurable and continuous at each strictly increasing $x$." Only the continuity clause is formalized: measurability refers to the Borel σ-field of the $J_1$ topology, which this series does not construct (it must not be replaced by measurability for the product σ-algebra on $\mathbb R^{\mathbb R}$, a different statement). Continuity is sequential (the space is metrizable, Theorem 2.6). The paths $x_n$ are in $E$ because the map is defined only on $E$. The statement is in $J_1$ only; the $M_1$ origin convention of the mission does not enter it.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), Theorem 7.2, p. 82

import Mathlib
import Definitions.Def_WhittFLT_FirstPassage_FirstPassage

namespace WhittFLT.FirstPassage

open Set Filter Topology

/-- Whitt (1980), Theorem 7.2, p. 82 (continuity clause): the first passage time function mapping
`E(J₁)` into `E ∩ D₀(J₁)` is continuous at each strictly increasing `x`. -/
theorem theorem_7_2 (xs : ℕ → ℝ → ℝ) (x : ℝ → ℝ)
    (hxs : ∀ n, InE (xs n)) (hx : InE x) (hmono : StrictMonoOn x (Ici 0))
    (hconv : WhittFLT.Composition.J1Tendsto (Ici 0) xs x) :
    WhittFLT.Composition.J1Tendsto (Ici 0) (fun n => firstPassage (xs n)) (firstPassage x) := by sorry

end WhittFLT.FirstPassage
