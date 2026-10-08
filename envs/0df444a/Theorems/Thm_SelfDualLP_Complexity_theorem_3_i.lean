-- Prove2me | Theorems.Thm_SelfDualLP_Complexity_theorem_3_i
-- name    : SelfDualLP.Complexity.theorem_3_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:58:44.199672+00:00
-- url     : https://prove2.me/theorems/bd0df4a2-44b2-43a1-a6e7-f2700b142375
-- title:
--   Theorem 3 (i) — (LP) has a solution iff $\tau^*>0$, and then $x^*/\tau^*$ and $(y^*/\tau^*,s^*/\tau^*)$ are optimal
-- statement:
--   Work under the choice (7). Let $(y^*,x^*,\tau^*,\theta^*=0,s^*,\kappa^*)$ be a strictly self-complementary solution for (HLP). Then
--
--   1. (LP) has a solution (an optimal solution) if and only if $\tau^*>0$;
--   2. in this case $x^*/\tau^*$ is an optimal solution for (LP) and $(y^*/\tau^*,\,s^*/\tau^*)$ is an optimal solution for (LD).
--
--   This is how a solution of the artificial program solves the original pair.
--
--   **Formalization Note** "(LP) has a solution (feasible and bounded)" is read as "(LP) has an optimal solution" (for linear programs these are equivalent, but the equivalence is not assumed).
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), p. 58, Theorem 3 (i)

import Mathlib
import Definitions.Def_SelfDualLP_Complexity_LPData
import Definitions.Def_SelfDualLP_Complexity_HLP

open Matrix

namespace SelfDualLP.Complexity

/-- Theorem 3 (i) (p. 58), under the choice (7). Let `(y*, x*, τ*, θ* = 0, s*, κ*)` be a
strictly self-complementary solution of (HLP). Then (LP) has a solution (an optimal solution)
if and only if `τ* > 0`; in this case `x*/τ*` is optimal for (LP) and `(y*/τ*, s*/τ*)` is
optimal for (LD). -/
theorem theorem_3_i {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (z : HLPPoint m n) (hz : StrictlySelfComplementary7 A b c z) :
    (LPHasSolution A b c ↔ 0 < z.τ) ∧
    (0 < z.τ → LPOptimal A b c (z.τ⁻¹ • z.x) ∧ LDOptimal A b c (z.τ⁻¹ • z.y) (z.τ⁻¹ • z.s)) := by sorry

end SelfDualLP.Complexity
