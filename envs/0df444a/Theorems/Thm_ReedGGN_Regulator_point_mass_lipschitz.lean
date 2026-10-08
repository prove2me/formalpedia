-- Prove2me | Theorems.Thm_ReedGGN_Regulator_point_mass_lipschitz
-- name    : ReedGGN.Regulator.point_mass_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:50:59.659036+00:00
-- url     : https://prove2.me/theorems/e971d688-2da9-4c48-a88c-53bb375e1758
-- title:
--   Proof of Proposition 3.1, (A.2) — for B concentrated at c > 0, ‖z₁ − z₂‖_t = ‖x₁ − x₂‖_t on [0, c) and ‖z₁ − z₂‖_t ≤ k ‖x₁ − x₂‖_t for (k−1)c ≤ t < kc
-- statement:
--   Let $c>0$, $a\in\mathbb R$, and $B=\mathbf 1\{\cdot\ge c\}$. Let $x_1,x_2$ be càdlàg inputs and $z_1,z_2$ càdlàg solutions of (3.1) with inputs $x_1,x_2$ respectively. Write $\|y\|_t=\sup_{0\le s\le t}|y(s)|$. Then
--   1. on the first window, $\|z_1-z_2\|_t=\|x_1-x_2\|_t$ for $0\le t<c$;
--   2. for every integer $k\ge1$ and every $t$ with $(k-1)c\le t<kc$,
--   $$\|z_1-z_2\|_t\le k\,\|x_1-x_2\|_t .$$
--
--   This is the Lipschitz continuity of the regulator map $\varphi^a_B$ on bounded intervals in the point-mass case, with constant $k$ on $[0,kc)$.
--
--   **Formalization Note** The paper's induction step is written "for $k<t\le(k+1)c$"; it means $kc\le t<(k+1)c$, the next window of (A.2), and that is what is stated (for all $k\ge1$ at once).
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, p. 32, proof of Proposition 3.1, Eq. (A.2)

import Mathlib
import Definitions.Def_ReedGGN_Regulator_PathSpace
import Definitions.Def_ReedGGN_Regulator_Equation

namespace ReedGGN.Regulator

open MeasureTheory

/-- Proof of Proposition 3.1, p. 32, (A.2): when `B` is concentrated on `c > 0`, for càdlàg
solutions `z₁, z₂` of (3.1) with càdlàg inputs `x₁, x₂`: `‖z₁ − z₂‖_t = ‖x₁ − x₂‖_t` for
`0 ≤ t < c`, and for every integer `k ≥ 1` and every `(k − 1)c ≤ t < kc`,
`‖z₁ − z₂‖_t ≤ k ‖x₁ − x₂‖_t`. -/
theorem point_mass_lipschitz (c a : ℝ) (hc : 0 < c) (x₁ x₂ z₁ z₂ : ℝ → ℝ)
    (hx₁ : IsCadlag x₁) (hx₂ : IsCadlag x₂) (hz₁ : IsCadlag z₁) (hz₂ : IsCadlag z₂)
    (h₁ : SolvesRegulator (Measure.dirac c) a x₁ z₁)
    (h₂ : SolvesRegulator (Measure.dirac c) a x₂ z₂) :
    (∀ t : ℝ, 0 ≤ t → t < c → supNorm t (z₁ - z₂) = supNorm t (x₁ - x₂)) ∧
    ∀ k : ℕ, 1 ≤ k → ∀ t : ℝ, ((k : ℝ) - 1) * c ≤ t → t < k * c →
      supNorm t (z₁ - z₂) ≤ k * supNorm t (x₁ - x₂) := by sorry

end ReedGGN.Regulator
