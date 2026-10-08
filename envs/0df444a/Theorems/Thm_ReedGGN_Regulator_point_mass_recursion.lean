-- Prove2me | Theorems.Thm_ReedGGN_Regulator_point_mass_recursion
-- name    : ReedGGN.Regulator.point_mass_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:51:01.409418+00:00
-- url     : https://prove2.me/theorems/229846d0-57a9-4cd5-8224-be71b4cc3a01
-- title:
--   Proof of Proposition 3.1, (A.1) — for B concentrated at c > 0, (3.1) is the recursion z = x on [0, c), z(t) = x(t) + (z(t−c)+a)⁺, and the solution is unique
-- statement:
--   Let $c>0$, $a\in\mathbb R$, and let $B=\mathbf 1\{\cdot\ge c\}$ be the distribution function of the unit mass at $c$.
--
--   1. For any functions $x,z$, the path $z$ solves (3.1),
--   $$z(t)=x(t)+\int_{[0,t]}(z(t-s)+a)^+\,dB(s),\quad t\ge0,$$
--   if and only if
--   $$z(t)=x(t)\ \ (0\le t<c)\qquad\text{and}\qquad z(t)=x(t)+(z(t-c)+a)^+\ \ (t\ge c).$$
--   2. Consequently, for a càdlàg input $x$, two càdlàg solutions of (3.1) coincide on $[0,\infty)$.
--
--   This is the degenerate case of the paper's proof of Proposition 3.1, where (3.1) reduces to an explicit recursion with step $c$.
--
--   **Formalization Note** The paper writes "it is clear that the solution to (3.1) satisfies the recursion ... in which case it is clearly unique"; item 1 makes the reduction an equivalence and item 2 states the uniqueness up to equality on $[0,\infty)$ (values at negative times are not part of a path).
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, p. 32, proof of Proposition 3.1, Eq. (A.1)

import Mathlib
import Definitions.Def_ReedGGN_Regulator_PathSpace
import Definitions.Def_ReedGGN_Regulator_Equation

namespace ReedGGN.Regulator

open MeasureTheory

/-- Proof of Proposition 3.1, p. 32, (A.1): when `B` is concentrated on a point `c > 0`,
a function `z` solves (3.1) iff `z = x` on `[0, c)` and `z(t) = x(t) + (z(t − c) + a)^+` for
`t ≥ c`; and two càdlàg solutions agree on `[0, ∞)`. -/
theorem point_mass_recursion (c a : ℝ) (hc : 0 < c) :
    (∀ x z : ℝ → ℝ, SolvesRegulator (Measure.dirac c) a x z ↔
      ((∀ t, 0 ≤ t → t < c → z t = x t) ∧
        (∀ t, c ≤ t → z t = x t + max (z (t - c) + a) 0))) ∧
    (∀ x z₁ z₂ : ℝ → ℝ, IsCadlag x → IsCadlag z₁ → IsCadlag z₂ →
      SolvesRegulator (Measure.dirac c) a x z₁ → SolvesRegulator (Measure.dirac c) a x z₂ →
      Set.EqOn z₁ z₂ (Set.Ici 0)) := by sorry

end ReedGGN.Regulator
