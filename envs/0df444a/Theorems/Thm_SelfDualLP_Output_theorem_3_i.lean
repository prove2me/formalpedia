-- Prove2me | Theorems.Thm_SelfDualLP_Output_theorem_3_i
-- name    : SelfDualLP.Output.theorem_3_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:27:47.824983+00:00
-- url     : https://prove2.me/theorems/1d00652b-ce62-47dd-81a5-6eb2498b447c
-- title:
--   Theorem 3 (i) — (LP) has a solution iff τ* > 0, and then x*/τ* and (y*/τ*, s*/τ*) are optimal
-- statement:
--   Work with (HLP) under the choice (7). Let $(y^*,x^*,\tau^*,\theta^*=0,s^*,\kappa^*)$ be a strictly self-complementary solution of (HLP). Then
--
--   1. (LP) has a solution (feasible and bounded) if and only if $\tau^*>0$;
--   2. in this case $x^*/\tau^*$ is an optimal solution of (LP) and $(y^*/\tau^*,\,s^*/\tau^*)$ is an optimal solution of (LD).
--
--   This is how the self-dual embedding recovers optimal solutions of the original pair from a solution of (HLP).
--
--   **Formalization Note** "(LP) has a solution (feasible and bounded)" is formalized as "(LP) has an optimal solution". For linear programs the two are equivalent, but the equivalence is itself a theorem.
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), p. 58, Theorem 3 (i); DOI 10.1287/moor.19.1.53

import Mathlib
import Definitions.Def_SelfDualLP_Complexity_LPData
import Definitions.Def_SelfDualLP_Output_HLP
import Definitions.Def_SelfDualLP_Output_Neighborhood
import Definitions.Def_SelfDualLP_Output_PCSequence

open Matrix

namespace SelfDualLP.Output

/-- Theorem 3 (i) (p. 58), under the choice (7). Let `(y*, x*, τ*, θ* = 0, s*, κ*)` be a
strictly self-complementary solution of (HLP). Then (LP) has a solution (an optimal solution)
if and only if `τ* > 0`; in this case `x*/τ*` is optimal for (LP) and `(y*/τ*, s*/τ*)` is
optimal for (LD). -/
theorem theorem_3_i {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (z : HLPPoint m n) (hz : StrictlySelfComplementary7 A b c z) :
    (SelfDualLP.Complexity.LPHasSolution A b c ↔ 0 < z.τ) ∧
    (0 < z.τ → SelfDualLP.Complexity.LPOptimal A b c (z.τ⁻¹ • z.x) ∧ SelfDualLP.Complexity.LDOptimal A b c (z.τ⁻¹ • z.y) (z.τ⁻¹ • z.s)) := by sorry
end SelfDualLP.Output
