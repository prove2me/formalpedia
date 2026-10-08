-- Prove2me | Theorems.Thm_PHLowerBound_TwoStage_pha_lower_bound
-- name    : PHLowerBound.TwoStage.pha_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:33:03.913299+00:00
-- url     : https://prove2.me/theorems/505435ac-6c52-4d0d-ba53-fe5454d82e6e
-- title:
--   §3.1 — every PHA price vector yields a lower bound
-- statement:
--   Let a finite-support two-stage SMIP have a feasible, attained finite optimum $z^*$ and nonempty scenario sets $X(\xi)$. Run Algorithm 1 through any iteration $N\ge1$, starting with zero prices and using its exact scenario minimizers, aggregation, and price updates. Its scenario dual bound satisfies
--
--   $$D(w^N)=\sum_{\xi\in\Xi}p_\xi\inf_{(x,y)\in X(\xi)}\bigl(c^\top x+g(\xi)^\top y+w^N(\xi)^\top x\bigr)\le z^*.$$
--
--   Thus a lower bound on the optimal cost is available after every completed price update of progressive hedging, regardless of whether its first-stage scenario decisions have converged.
--
--   **Formalization Note** A finite run prefix records all of Algorithm 1's exact minimization clauses through $N$. Its final price vector is computed at iteration $N$; Step 6 can stop the run there. The page does not restrict the sign of $\rho$, and neither does the theorem.
-- source:
--   Gade et al., Obtaining Lower Bounds from the Progressive Hedging Algorithm for Stochastic Mixed-Integer Programs, author manuscript SAND2013-9195J (OSTI 1310314), p. 7, §3.1, paragraph after Proposition 1, with p. 6, Proposition 1

import Mathlib
import Definitions.Def_PHLowerBound_TwoStage_Setting

namespace PHLowerBound.TwoStage

attribute [local instance] Classical.decEq

theorem pha_lower_bound {Ξ : Type*} [Fintype Ξ]
    {n₁ p₁ n₂ p₂ m₁ m₂ : ℕ} (P : SMIP Ξ n₁ p₁ n₂ p₂ m₁ m₂)
    (hX : ∀ ξ, (P.X ξ).Nonempty) (hopt : P.HasOptimalSolution)
    (ρ : ℝ) (x : ℕ → Ξ → Fin n₁ → ℝ) (y : ℕ → Ξ → Fin n₂ → ℝ)
    (xhat : ℕ → Fin n₁ → ℝ) (w : ℕ → Ξ → Fin n₁ → ℝ)
    (N : ℕ) (hN : 1 ≤ N) (hrun : P.IsPHARun ρ x y xhat w N) :
    P.D (w N) ≤ P.zStar := by sorry

end PHLowerBound.TwoStage
