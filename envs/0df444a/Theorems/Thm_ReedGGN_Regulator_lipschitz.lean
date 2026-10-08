-- Prove2me | Theorems.Thm_ReedGGN_Regulator_lipschitz
-- name    : ReedGGN.Regulator.lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:51:04.445373+00:00
-- url     : https://prove2.me/theorems/afbb2f1a-54d9-4e75-936b-ea02b7e64934
-- title:
--   Proof of Proposition 3.1, Lipschitz continuity — ‖z₂ − z₁‖_{kδ} ≤ (1 − ε)^{−k} ‖x₂ − x₁‖_{kδ}
-- statement:
--   Let $B$, $\mu$, $a$, $\delta>0$ and $0<\varepsilon<1$ be as in the uniqueness milestone: $B(y+\delta)-B(y)<\varepsilon$ for all $y\ge0$ and $\mu([0,\delta])<\varepsilon$. Let $x_1,x_2$ be càdlàg and let $z_1,z_2$ be càdlàg solutions of (3.1) with inputs $x_1,x_2$. Then for every integer $k\ge1$,
--   $$\|z_2-z_1\|_{k\delta}\le (1-\varepsilon)^{-k}\,\|x_2-x_1\|_{k\delta}.$$
--
--   Since every $T\ge0$ satisfies $T\le k\delta$ for some $k$, this is the Lipschitz continuity of $\varphi^a_B$ in the topology of uniform convergence on bounded intervals, in the non-degenerate case.
--
--   **Formalization Note** The paper writes out $k=1$ and $k=2$ and then "iterating the above argument"; the statement is the general $k$.
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, p. 34, proof of Proposition 3.1 (Lipschitz continuity); standing hypothesis p. 32

import Mathlib
import Definitions.Def_ReedGGN_Regulator_PathSpace
import Definitions.Def_ReedGGN_Regulator_Equation

namespace ReedGGN.Regulator

open MeasureTheory

/-- Proof of Proposition 3.1, Lipschitz continuity (p. 34): under the window condition of the
non-degenerate case, for càdlàg solutions `z₁, z₂` of (3.1) with càdlàg inputs `x₁, x₂` and
every integer `k ≥ 1`, `‖z₂ − z₁‖_{kδ} ≤ (1 − ε)^{−k} ‖x₂ − x₁‖_{kδ}`. -/
theorem lipschitz (μ : Measure ℝ) [IsProbabilityMeasure μ] (a δ ε : ℝ)
    (hδ : 0 < δ) (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hB₀ : μ (Set.Icc 0 δ) < ENNReal.ofReal ε)
    (hB : ∀ y, 0 ≤ y → μ (Set.Ioc y (y + δ)) < ENNReal.ofReal ε)
    (x₁ x₂ z₁ z₂ : ℝ → ℝ)
    (hx₁ : IsCadlag x₁) (hx₂ : IsCadlag x₂) (hz₁ : IsCadlag z₁) (hz₂ : IsCadlag z₂)
    (h₁ : SolvesRegulator μ a x₁ z₁) (h₂ : SolvesRegulator μ a x₂ z₂) :
    ∀ k : ℕ, 1 ≤ k →
      supNorm (k * δ) (z₂ - z₁) ≤ (1 - ε)⁻¹ ^ k * supNorm (k * δ) (x₂ - x₁) := by sorry

end ReedGGN.Regulator
