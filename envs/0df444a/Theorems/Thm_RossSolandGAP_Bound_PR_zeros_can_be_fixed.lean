-- Prove2me | Theorems.Thm_RossSolandGAP_Bound_PR_zeros_can_be_fixed
-- name    : RossSolandGAP.Bound.PR_zeros_can_be_fixed
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:10:16.818378+00:00
-- url     : https://prove2.me/theorems/88ed3c4a-0124-4e67-8caa-408b03fc7235
-- title:
--   §2, p. 96 — at λ_j = c_2j the variables that are zero in the (PR) solution can be set to zero in (PR_λ)
-- statement:
--   Let $m\ge2$, let $r_{ij}\ge0$, let $j\mapsto i_j$ be a cheapest-agent selection, and take the multipliers $\lambda_j=c_{2j}$, the second smallest of $c_{1j},\dots,c_{mj}$. Let $x$ be feasible for (PR$_\lambda$) (binary, with $\sum_j r_{ij}x_{ij}\le b_i$ for every agent $i$). Define $x'$ by keeping $x_{ij}$ when $i=i_j$ and setting $x'_{ij}=0$ when $i\ne i_j$, i.e. when $x_{ij}$ is zero in the (PR) solution. Then $x'$ is feasible for (PR$_\lambda$) and
--
--   $$
--   \sum_{i}\sum_{j}c_{ij}x'_{ij}+\sum_{j}c_{2j}\Bigl(1-\sum_{i}x'_{ij}\Bigr)\ \le\ \sum_{i}\sum_{j}c_{ij}x_{ij}+\sum_{j}c_{2j}\Bigl(1-\sum_{i}x_{ij}\Bigr).
--   $$
--
--   So, at these multipliers, (PR$_\lambda$) may be solved over points supported on the (PR) assignment pattern. This is the third observation in the paper's verification of its principal result.
--
--   **Formalization Note** $r_{ij}\ge0$ is implicit in the paper ("the resource required by agent $i$ to do task $j$") and is needed: it is what keeps $x'$ within the budgets. Agents and tasks are 0-based.
-- source:
--   Ross & Soland, A Branch and Bound Algorithm for the Generalized Assignment Problem, Mathematical Programming 8, 1975, p. 96, §2, second paragraph, second sentence (third observation)

import Mathlib
import Definitions.Def_RossSolandGAP_Bound_Model
open Finset

namespace RossSolandGAP.Bound

theorem PR_zeros_can_be_fixed {m n : ℕ} (hm : 1 < m) (c r : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (hr : ∀ i j, 0 ≤ r i j) (a : Fin n → Fin m) (ha : IsCheapest c a)
    (x : Fin m → Fin n → ℝ) (hx : FeasibleLag r b x) :
    FeasibleLag r b (fun i j => if a j = i then x i j else 0) ∧
    lagObj c (c2 hm c a) (fun i j => if a j = i then x i j else 0) ≤
      lagObj c (c2 hm c a) x := by sorry

end RossSolandGAP.Bound
