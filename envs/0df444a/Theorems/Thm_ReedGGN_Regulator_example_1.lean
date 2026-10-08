-- Prove2me | Theorems.Thm_ReedGGN_Regulator_example_1
-- name    : ReedGGN.Regulator.example_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:51:24.856179+00:00
-- url     : https://prove2.me/theorems/ba1bed8f-e7b7-40ce-91c7-ea23b7c5da51
-- title:
--   Example 1, (4.17)–(4.19) — with deterministic unit service times the fluid equation has the sawtooth solution Q̄(t) = 1 + t − ⌊t⌋
-- statement:
--   Take deterministic unit service times, $F_0(x)=F(x)=\mathbf 1\{x\ge1\}$ (the law of the unit mass at $1$), initial fluid content $\bar Q_0=1$ and fluid arrivals $\bar A=e$. The fluid equation (4.7) then reads
--   $$\bar Q(t)=\min(1,1)\bar F_0(t)+(1-1)^+G(t)+\int_0^tG(t-s)\,ds+\int_{[0,t]}(\bar Q(t-s)-1)^+\,dF(s),\qquad t\ge0,$$
--   with $\bar F_0=G=1-F$. Then:
--
--   1. the path $\bar Q(t)=1+t-\lfloor t\rfloor$ is càdlàg on $[0,\infty)$;
--   2. it solves this equation;
--   3. every càdlàg solution of the equation equals $1+t-\lfloor t\rfloor$ for all $t\ge0$.
--
--   This verifies the paper's Example 1, the explicit sawtooth fluid limit (4.19), periodic with period $1$ and discontinuous at the integers.
--
--   **Formalization Note** The input terms of (4.7) are written as on p. 12 and not pre-simplified: that they equal $1+t$ on $[0,1)$ and $1$ afterwards is part of the claim. The paper's (4.18) reads $\bar Q(t)=1+(\bar Q(t)-1)^+$, which every $\bar Q\ge1$ satisfies; (4.7) gives $\bar Q(t)=1+(\bar Q(t-1)-1)^+$ for $t\ge1$, which is the equation stated here. Theorem 4.1 itself (the fluid limit) is not part of this statement.
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, p. 15, Example 1, Eqs. (4.17)–(4.19); p. 12, Eq. (4.7)

import Mathlib
import Definitions.Def_ReedGGN_Regulator_PathSpace
import Definitions.Def_ReedGGN_Regulator_Equation
import Definitions.Def_ReedGGN_Regulator_FluidInput

namespace ReedGGN.Regulator

open MeasureTheory

/-- Example 1 (p. 15), (4.17)–(4.19): deterministic service times `F_0 = F = 1{x ≥ 1}`,
`Q̄₀ = 1`, `Ā = e`. The fluid equation (4.7) is (3.1) with `B = F`, `a = −1` and input the
first three terms of (4.7); its càdlàg solution is `Q̄(t) = 1 + t − ⌊t⌋` on `[0, ∞)`. -/
theorem example_1 :
    IsCadlag (fun t : ℝ => 1 + t - (⌊t⌋ : ℝ)) ∧
    SolvesRegulator (Measure.dirac 1) (-1)
      (fluidInput 1 (tail (Measure.dirac 1)) (Measure.dirac 1))
      (fun t : ℝ => 1 + t - (⌊t⌋ : ℝ)) ∧
    (∀ Q : ℝ → ℝ, IsCadlag Q →
      SolvesRegulator (Measure.dirac 1) (-1)
        (fluidInput 1 (tail (Measure.dirac 1)) (Measure.dirac 1)) Q →
      Set.EqOn Q (fun t : ℝ => 1 + t - (⌊t⌋ : ℝ)) (Set.Ici 0)) := by sorry

end ReedGGN.Regulator
