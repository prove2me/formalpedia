-- Prove2me | Theorems.Thm_ReedGGN_Regulator_uniqueness
-- name    : ReedGGN.Regulator.uniqueness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:51:41.489751+00:00
-- url     : https://prove2.me/theorems/81fb80e3-2e3e-4c5b-9534-1f67a1979e46
-- title:
--   Proof of Proposition 3.1, Uniqueness — if B(y+δ) − B(y) < ε < 1 for all y ≥ 0, two càdlàg solutions of (3.1) coincide
-- statement:
--   Let $B$ be a distribution function on $\mathbb R$ with law $\mu$, and $a\in\mathbb R$. Suppose there are $\delta>0$ and $0<\varepsilon<1$ such that
--   $$B(y+\delta)-B(y)<\varepsilon\quad\text{for all } y\ge0,\qquad\text{and}\qquad \mu([0,\delta])<\varepsilon .$$
--   Let $x$ be càdlàg and let $u,v$ be càdlàg solutions of (3.1) with input $x$. Then $u(t)=v(t)$ for all $t\ge0$.
--
--   This is the uniqueness half of Proposition 3.1 in the non-degenerate case of the paper's proof.
--
--   **Formalization Note** $B(y+\delta)-B(y)$ is $\mu((y,y+\delta])$. The second condition, $\mu([0,\delta])<\varepsilon$, is the bound the proof uses on the first window (it writes $B(\delta)<\varepsilon$ in (A.7)); with integrals over the closed interval $[0,t]$ it is the mass of $[0,\delta]$, an atom at $0$ included, and it is stated separately because the paper's condition is only about half-open windows $(y,y+\delta]$.
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, p. 34, proof of Proposition 3.1 (Uniqueness); standing hypothesis p. 32

import Mathlib
import Definitions.Def_ReedGGN_Regulator_PathSpace
import Definitions.Def_ReedGGN_Regulator_Equation

namespace ReedGGN.Regulator

open MeasureTheory

/-- Proof of Proposition 3.1, Uniqueness (p. 34): if `B(y + δ) − B(y) < ε` for all `y ≥ 0`
(and the first window `[0, δ]`, atom at `0` included, has mass `< ε`), with `0 < ε < 1`,
then two càdlàg solutions of (3.1) for the same càdlàg input agree on `[0, ∞)`. -/
theorem uniqueness (μ : Measure ℝ) [IsProbabilityMeasure μ] (a δ ε : ℝ)
    (hδ : 0 < δ) (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hB₀ : μ (Set.Icc 0 δ) < ENNReal.ofReal ε)
    (hB : ∀ y, 0 ≤ y → μ (Set.Ioc y (y + δ)) < ENNReal.ofReal ε)
    (x u v : ℝ → ℝ) (hx : IsCadlag x) (hu : IsCadlag u) (hv : IsCadlag v)
    (hsu : SolvesRegulator μ a x u) (hsv : SolvesRegulator μ a x v) :
    Set.EqOn u v (Set.Ici 0) := by sorry

end ReedGGN.Regulator
