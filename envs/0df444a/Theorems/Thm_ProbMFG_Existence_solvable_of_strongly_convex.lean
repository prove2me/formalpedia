-- Prove2me | Theorems.Thm_ProbMFG_Existence_solvable_of_strongly_convex
-- name    : ProbMFG.Existence.solvable_of_strongly_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:59.384425+00:00
-- url     : https://prove2.me/theorems/6bc2f9a5-afd7-4b9d-9212-b6709514d4b0
-- title:
--   §3.7 — solvability under strengthened convexity
-- statement:
--   Under (A.1)–(A.7) and the strengthened convexity condition (3.28) for some $\gamma>0$, the self-consistent McKean–Vlasov FBSDE (3.1) is solvable:
--   $$\exists(X,Y,Z)\text{ solving (3.1) with }\mu_t=\mathcal L(X_t).$$
--   This is the intermediate existence statement at the start of the paper's proof of Theorem 3.2.
-- source:
--   Carmona and Delarue, Probabilistic analysis of mean-field games, SIAM J. Control Optim. 51 (2013), p. 2723, §3.7, first sentence; https://doi.org/10.1137/120883499

import Mathlib
import Definitions.Def_ProbMFG_Existence_Model
import Definitions.Def_ProbMFG_Existence_Solution

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbMFG.Existence

/-- The first sentence of §3.7: (3.1) is solvable under (3.28). -/
theorem solvable_of_strongly_convex {d m k : ℕ} (M : Model d m k)
    (lam cL γ : ℝ) (hA : M.Assumptions lam cL) (hγ : M.StronglyConvexX lam γ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → Fin m → ℝ) (hW : Peng1990.SMP.IsStdBrownian P W) :
    ∃ (X Y : StateProcess Ω d) (Z : NoiseProcess Ω d m),
      M.SolvesMKV P hW X Y Z := by sorry

end ProbMFG.Existence
