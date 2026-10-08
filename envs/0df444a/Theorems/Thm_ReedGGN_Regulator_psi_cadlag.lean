-- Prove2me | Theorems.Thm_ReedGGN_Regulator_psi_cadlag
-- name    : ReedGGN.Regulator.psi_cadlag
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:51:41.941431+00:00
-- url     : https://prove2.me/theorems/b286be59-44a0-42ae-9b0d-5b8d75de2455
-- title:
--   Proof of Proposition 3.1, Measurability — Ψᵃ_B maps D[0,∞) into D[0,∞)
-- statement:
--   Let $B$ be a distribution function on $\mathbb R$ with law $\mu$, and $a\in\mathbb R$. For every path $u$ that is càdlàg on $[0,\infty)$, the path
--   $$\Psi^a_B(u)(t)=\int_{[0,t]}(u(t-s)+a)^+\,dB(s),\qquad t\ge 0,$$
--   is again càdlàg on $[0,\infty)$.
--
--   The paper defines $\Psi^a_B$ as a map $D[0,\infty)\to D[0,\infty)$ without comment; this statement is that claim.
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, p. 34, proof of Proposition 3.1 (Measurability), definition of Ψᵃ_B

import Mathlib
import Definitions.Def_ReedGGN_Regulator_PathSpace
import Definitions.Def_ReedGGN_Regulator_Equation

namespace ReedGGN.Regulator

open MeasureTheory

/-- Proof of Proposition 3.1, Measurability (p. 34): `Ψ^a_B` maps `D[0,∞)` into `D[0,∞)`:
for every càdlàg `u`, `t ↦ ∫_0^t (u(t − s) + a)^+ dB(s)` is càdlàg. -/
theorem psi_cadlag (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : ℝ) (u : ℝ → ℝ)
    (hu : IsCadlag u) : IsCadlag (psi μ a u) := by sorry

end ReedGGN.Regulator
