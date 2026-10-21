-- Prove2me | Theorems.Thm_ProcFlex_DMGI_duality_3
-- name    : ProcFlex.DMGI.duality_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:26:10.871661+00:00
-- url     : https://prove2.me/theorems/baa94749-3212-4420-a9a7-ef650cc4bfe7
-- title:
--   Equation (3): strong duality for the profit LP
-- statement:
--   Let $A$ be a flexibility design in a valid system, and let $d$ be a nonnegative demand vector. The maximum production profit $g(A,d)$ is the attained minimum of the dual program:
--
--   $$
--   g(A,d)=\min_{y,z\ge0}\left\{\sum_i d_i y_i+\sum_j C_jz_j:y_i+z_j\ge p_i\text{ for every }(j,i)\in A\right\}.
--   $$
--
--   This identifies the finite profit program with the dual values used to define the margin-group index.
--
--   **Formalization Note** The system assumptions include nonnegative capacities, positive occupied margin levels, and positive numbers of plants and products.
-- source:
--   Wang, Wang & Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 22 May 2020), p. 16, (3)

import Mathlib
import Definitions.Def_ProcFlex_DMGI_Model

namespace ProcFlex.DMGI

/-- Equation (3), p. 16: the profit LP equals the attained minimum of its dual. -/
theorem duality_3 {m n T : ℕ} (S : System m n T) (hS : S.IsValid)
    (A : Design m n) (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) :
    IsLeast {v : ℝ | ∃ (y : Fin n → ℝ) (z : Fin m → ℝ),
      DualFeasible S A y z ∧ v = dualObj S d y z} (g S A d) := by sorry

end ProcFlex.DMGI
