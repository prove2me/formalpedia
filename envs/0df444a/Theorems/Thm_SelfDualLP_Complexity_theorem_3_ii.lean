-- Prove2me | Theorems.Thm_SelfDualLP_Complexity_theorem_3_ii
-- name    : SelfDualLP.Complexity.theorem_3_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:58:42.33075+00:00
-- url     : https://prove2.me/theorems/d1493d3a-4ae8-459b-bea6-68b0ca129d8e
-- title:
--   Theorem 3 (ii) — if $\tau^*=0$, the sign of $c^Tx^*$ or $-b^Ty^*$ certifies infeasibility
-- statement:
--   Work under the choice (7). Let $(y^*,x^*,\tau^*,\theta^*=0,s^*,\kappa^*)$ be a strictly self-complementary solution for (HLP) with $\tau^*=0$. Then $\kappa^*>0$, which implies
--   $$
--   c^Tx^*-b^Ty^*<0,
--   $$
--   i.e. at least one of $c^Tx^*$ and $-b^Ty^*$ is strictly less than zero. Moreover
--
--   1. if $c^Tx^*<0$ then (LD) is infeasible;
--   2. if $-b^Ty^*<0$ then (LP) is infeasible;
--
--   so if both are negative, both (LP) and (LD) are infeasible.
--
--   This is the infeasibility certificate the algorithm returns when the original pair has no optimal solution.
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), p. 58, Theorem 3 (ii)

import Mathlib
import Definitions.Def_SelfDualLP_Complexity_LPData
import Definitions.Def_SelfDualLP_Complexity_HLP

open Matrix

namespace SelfDualLP.Complexity

/-- Theorem 3 (ii) (p. 58), under the choice (7). Let `(y*, x*, τ*, θ* = 0, s*, κ*)` be a
strictly self-complementary solution of (HLP) with `τ* = 0`. Then `κ* > 0`, hence
`cᵀx* − bᵀy* < 0`, i.e. at least one of `cᵀx*` and `−bᵀy*` is negative; if `cᵀx* < 0` then
(LD) is infeasible, if `−bᵀy* < 0` then (LP) is infeasible (so if both, both are). -/
theorem theorem_3_ii {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (z : HLPPoint m n) (hz : StrictlySelfComplementary7 A b c z) (hτ : z.τ = 0) :
    0 < z.κ ∧ c ⬝ᵥ z.x - b ⬝ᵥ z.y < 0 ∧ (c ⬝ᵥ z.x < 0 ∨ -(b ⬝ᵥ z.y) < 0) ∧
    (c ⬝ᵥ z.x < 0 → ¬ LDIsFeasible A c) ∧
    (-(b ⬝ᵥ z.y) < 0 → ¬ LPIsFeasible A b c) := by sorry

end SelfDualLP.Complexity
