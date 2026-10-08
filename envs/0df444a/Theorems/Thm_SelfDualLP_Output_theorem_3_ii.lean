-- Prove2me | Theorems.Thm_SelfDualLP_Output_theorem_3_ii
-- name    : SelfDualLP.Output.theorem_3_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:27:40.208294+00:00
-- url     : https://prove2.me/theorems/f9470ff3-551e-406b-a87e-8b95aab329d5
-- title:
--   Theorem 3 (ii) — if τ* = 0 then κ* > 0 and the sign of cᵀx* or −bᵀy* certifies infeasibility
-- statement:
--   Work with (HLP) under the choice (7). Let $(y^*,x^*,\tau^*,\theta^*=0,s^*,\kappa^*)$ be a strictly self-complementary solution of (HLP) with $\tau^*=0$. Then
--
--   1. $\kappa^*>0$, which implies $c^Tx^*-b^Ty^*<0$, i.e. at least one of $c^Tx^*$ and $-b^Ty^*$ is strictly less than zero;
--   2. if $c^Tx^*<0$ then (LD) is infeasible;
--   3. if $-b^Ty^*<0$ then (LP) is infeasible;
--   4. if both $c^Tx^*<0$ and $-b^Ty^*<0$ then both (LP) and (LD) are infeasible.
--
--   Together with Theorem 3 (i), this classifies the outcome of the self-dual embedding: optimal solutions, or a Farkas-type certificate of infeasibility.
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), p. 58, Theorem 3 (ii); DOI 10.1287/moor.19.1.53

import Mathlib
import Definitions.Def_SelfDualLP_Complexity_LPData
import Definitions.Def_SelfDualLP_Output_HLP
import Definitions.Def_SelfDualLP_Output_Neighborhood
import Definitions.Def_SelfDualLP_Output_PCSequence

open Matrix

namespace SelfDualLP.Output

/-- Theorem 3 (ii) (p. 58), under the choice (7). Let `(y*, x*, τ*, θ* = 0, s*, κ*)` be a
strictly self-complementary solution of (HLP) with `τ* = 0`. Then `κ* > 0`, hence
`cᵀx* − bᵀy* < 0`, i.e. at least one of `cᵀx*` and `−bᵀy*` is negative; if `cᵀx* < 0` then
(LD) is infeasible; if `−bᵀy* < 0` then (LP) is infeasible; and if both are negative then both
(LP) and (LD) are infeasible. -/
theorem theorem_3_ii {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (z : HLPPoint m n) (hz : StrictlySelfComplementary7 A b c z) (hτ : z.τ = 0) :
    0 < z.κ ∧ c ⬝ᵥ z.x - b ⬝ᵥ z.y < 0 ∧ (c ⬝ᵥ z.x < 0 ∨ -(b ⬝ᵥ z.y) < 0) ∧
    (c ⬝ᵥ z.x < 0 → ¬ SelfDualLP.Complexity.LDIsFeasible A c) ∧
    (-(b ⬝ᵥ z.y) < 0 → ¬ SelfDualLP.Complexity.LPIsFeasible A b c) ∧
    (c ⬝ᵥ z.x < 0 ∧ -(b ⬝ᵥ z.y) < 0 → ¬ SelfDualLP.Complexity.LPIsFeasible A b c ∧ ¬ SelfDualLP.Complexity.LDIsFeasible A c) := by sorry
end SelfDualLP.Output
