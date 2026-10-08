-- Prove2me | Theorems.Thm_ProbMFG_Existence_proposition_3_8
-- name    : ProbMFG.Existence.proposition_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:05:00.639856+00:00
-- url     : https://prove2.me/theorems/b9ddcb18-e836-4d43-93e2-ce3294d2e1bc
-- title:
--   Proposition 3.8 — existence with bounded spatial gradients
-- statement:
--   Assume (A.1)–(A.7). If a constant $c_B>0$ bounds the spatial gradients of both costs, uniformly over the allowed times, states, controls and finite-second-moment laws,
--   $$\|\partial_x f(t,x,\mu,a)\|\le c_B,\qquad \|\partial_x g(x,\mu)\|\le c_B,$$
--   then the self-consistent McKean–Vlasov FBSDE (3.1) has a solution on the given Brownian probability space.
--
--   This is the bounded-gradient existence case used before passing to general costs.
-- source:
--   Carmona and Delarue, Probabilistic analysis of mean-field games, SIAM J. Control Optim. 51 (2013), p. 2716, Proposition 3.8 and (3.8); https://doi.org/10.1137/120883499

import Mathlib
import Definitions.Def_ProbMFG_Existence_Model
import Definitions.Def_ProbMFG_Existence_Solution

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbMFG.Existence

/-- Proposition 3.8: solvability with uniformly bounded spatial cost gradients. -/
theorem proposition_3_8 {d m k : ℕ} (M : Model d m k) (lam cL : ℝ)
    (hA : M.Assumptions lam cL) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → Fin m → ℝ) (hW : Peng1990.SMP.IsStdBrownian P W)
    (cB : ℝ) (hcB : 0 < cB)
    (hBound : ∀ t ≤ M.T, ∀ x μ a, IsP2 μ →
      ‖M.dgx x μ‖ ≤ cB ∧ ‖M.dfx t x μ a‖ ≤ cB) :
    ∃ (X Y : StateProcess Ω d) (Z : NoiseProcess Ω d m),
      M.SolvesMKV P hW X Y Z := by sorry

end ProbMFG.Existence
