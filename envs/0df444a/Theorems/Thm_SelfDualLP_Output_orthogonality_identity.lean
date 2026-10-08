-- Prove2me | Theorems.Thm_SelfDualLP_Output_orthogonality_identity
-- name    : SelfDualLP.Output.orthogonality_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:27:40.967702+00:00
-- url     : https://prove2.me/theorems/23612c58-2f90-4da0-b1d0-4e521f5767ce
-- title:
--   Proof of Theorem 8 — (xᵏ − x*)ᵀ(sᵏ − s*) + (τᵏ − τ*)(κᵏ − κ*) = 0 and xᵏᵀs* + sᵏᵀx* + κᵏτ* = (n+1)μᵏ = (n+1)θᵏ
-- statement:
--   Work with (HLP) under the choice (7). Let $(y,x,\tau,\theta,s,\kappa)\in\mathcal F_h$ be a feasible point, and let $(y^*,x^*,\tau^*,\theta^*,s^*,\kappa^*)$ be a self-complementary (optimal) solution of (HLP) with $\kappa^*=0$. Then
--
--   $$
--   (x-x^*)^T(s-s^*)+(\tau-\tau^*)(\kappa-\kappa^*)=0,
--   $$
--
--   and this can be rewritten as
--
--   $$
--   x^Ts^*+s^Tx^*+\kappa\tau^*=(n+1)\mu=(n+1)\theta,\qquad \mu=\frac{x^Ts+\tau\kappa}{n+1}.
--   $$
--
--   In the proof of Theorem 8 it is applied with the iterate $z^k$ in place of $(y,x,\tau,\theta,s,\kappa)$; dropping the nonnegative terms $x^Ts^*$ and $s^Tx^*$ gives $\kappa^k\tau^*\le(n+1)\mu^k$.
--
--   **Formalization Note** The first equality holds for any two points of $\mathcal F_h$. The rewritten form uses that the second point is optimal (so $\theta^*=0$ and $(x^*)^Ts^*+\tau^*\kappa^*=0$ by Theorem 2 (iv)) and that $\kappa^*=0$; these are exactly the hypotheses of the statement.
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), p. 63, proof of Theorem 8; DOI 10.1287/moor.19.1.53

import Mathlib
import Definitions.Def_SelfDualLP_Complexity_LPData
import Definitions.Def_SelfDualLP_Output_HLP
import Definitions.Def_SelfDualLP_Output_Neighborhood
import Definitions.Def_SelfDualLP_Output_PCSequence

open Matrix

namespace SelfDualLP.Output

/-- Proof of Theorem 8 (p. 63), orthogonality identity, under (7). Let `z = (y, x, τ, θ, s, κ) ∈ 𝓕_h`
and let `w = (y*, x*, τ*, θ*, s*, κ*)` be a self-complementary (optimal) solution of (HLP) with
`κ* = 0`. Then `(x − x*)ᵀ(s − s*) + (τ − τ*)(κ − κ*) = 0`, which can be rewritten as
`xᵀs* + sᵀx* + κτ* = (n + 1)μ = (n + 1)θ`, where `μ = (xᵀs + τκ)/(n + 1)`. -/
theorem orthogonality_identity {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (z w : HLPPoint m n) (hz : HLPFeasible7 A b c z)
    (hw : HLPOptimal7 A b c w) (hκ : w.κ = 0) :
    (z.x - w.x) ⬝ᵥ (z.s - w.s) + (z.τ - w.τ) * (z.κ - w.κ) = 0 ∧
    z.x ⬝ᵥ w.s + z.s ⬝ᵥ w.x + z.κ * w.τ = ((n : ℝ) + 1) * mu z ∧
    ((n : ℝ) + 1) * mu z = ((n : ℝ) + 1) * z.θ := by sorry
end SelfDualLP.Output
