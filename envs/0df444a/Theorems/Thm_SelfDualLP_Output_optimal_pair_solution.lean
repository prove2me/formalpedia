-- Prove2me | Theorems.Thm_SelfDualLP_Output_optimal_pair_solution
-- name    : SelfDualLP.Output.optimal_pair_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:27:31.892095+00:00
-- url     : https://prove2.me/theorems/3fc53527-6b1d-47bd-af5a-a53bcae8e342
-- title:
--   Proof of Theorem 8 — an optimal (LP)/(LD) pair, scaled by α = (n+1)/(eᵀx̄ + eᵀs̄ + 1), is a self-complementary solution of (HLP)
-- statement:
--   Work with (HLP) under the choice (7). Let $\bar x$ be an optimal solution of (LP) and $(\bar y,\bar s)$ an optimal solution of (LD) (with $\bar s=c-A^T\bar y$). Put
--
--   $$
--   \alpha=\frac{n+1}{e^T\bar x+e^T\bar s+1}.
--   $$
--
--   Then $\alpha>0$, and the point
--
--   $$
--   y^*=\alpha\bar y,\quad x^*=\alpha\bar x,\quad \tau^*=\alpha,\quad \theta^*=0,\quad s^*=\alpha\bar s,\quad \kappa^*=0
--   $$
--
--   is a self-complementary (that is, optimal) solution of (HLP).
--
--   In the proof of Theorem 8 this solution is compared with the iterates; its component $\tau^*=\alpha$ produces the lower bound $(1-2\beta)/(e^T\bar x+e^T\bar s+1)$ on $\tau^k$.
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), p. 63, proof of Theorem 8; DOI 10.1287/moor.19.1.53

import Mathlib
import Definitions.Def_SelfDualLP_Complexity_LPData
import Definitions.Def_SelfDualLP_Output_HLP
import Definitions.Def_SelfDualLP_Output_Neighborhood
import Definitions.Def_SelfDualLP_Output_PCSequence

open Matrix

namespace SelfDualLP.Output

/-- Proof of Theorem 8 (p. 63): if `x̄` is optimal for (LP) and `(ȳ, s̄)` is optimal for (LD), then
with `α = (n + 1)/(eᵀx̄ + eᵀs̄ + 1) > 0` the point
`(y*, x*, τ*, θ*, s*, κ*) = (αȳ, αx̄, α, 0, αs̄, 0)` is a self-complementary (i.e. optimal)
solution of (HLP) under (7). -/
theorem optimal_pair_solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (xbar : Fin n → ℝ) (ybar : Fin m → ℝ) (sbar : Fin n → ℝ)
    (hx : SelfDualLP.Complexity.LPOptimal A b c xbar) (hy : SelfDualLP.Complexity.LDOptimal A b c ybar sbar) :
    0 < ((n : ℝ) + 1) / (ones n ⬝ᵥ xbar + ones n ⬝ᵥ sbar + 1) ∧
    HLPOptimal7 A b c
      (let α : ℝ := ((n : ℝ) + 1) / (ones n ⬝ᵥ xbar + ones n ⬝ᵥ sbar + 1)
       ⟨α • ybar, α • xbar, α, 0, α • sbar, 0⟩) := by sorry
end SelfDualLP.Output
