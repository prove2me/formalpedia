-- Prove2me | Theorems.Thm_SimpsonInv_Vertex_theorem_II
-- name    : SimpsonInv.Vertex.theorem_II
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:27:00.176206+00:00
-- url     : https://prove2.me/theorems/1661bcac-197e-40ba-b942-5c4514213ba1
-- title:
--   THEOREM II, p. 869 — setting Sⱼ = Sⱼ₋₁ + Tⱼ gives the cost of the model with operations j, j+1 coupled
-- statement:
--   Consider a model with $n$ operations, $n - 1$ variables $S_1, \dots, S_{n-1}$, constants $c, S_0, S_n$ and $r_i, T_i$ ($1 \le i \le n$), and cost
--   $$
--   f(S_1, \dots, S_{n-1}) = c + \sum_{i=1}^{n} r_i \sqrt{S_{i-1} - S_i + T_i}.
--   $$
--   Fix $j$ with $1 \le j \le n - 1$ and suppose $S_j = S_{j-1} + T_j$, i.e. the average inventory $I_j$ is zero. Form the **coupled model** with $n - 1$ operations: inventory point $I_j$ is removed, operations $j$ and $j+1$ become one operation with processing time $T_j + T_{j+1}$, so
--   $$
--   T'_i = \begin{cases} T_i & i < j,\\ T_j + T_{j+1} & i = j,\\ T_{i+1} & i > j,\end{cases}
--   \qquad
--   r'_i = \begin{cases} r_i & i < j,\\ r_{i+1} & i \ge j,\end{cases}
--   $$
--   and its variables are $(S_1, \dots, S_{j-1}, S_{j+1}, \dots, S_{n-1})$, with the same end constants $S_0, S_n$. Then the original cost equals the coupled model's cost $f'$ (the same formula with $n - 1$ operations and data $T', r'$):
--   $$
--   f(S_1, \dots, S_{n-1}) = f'(S_1, \dots, S_{j-1}, S_{j+1}, \dots, S_{n-1}).
--   $$
--
--   The theorem says a vanishing inventory can be removed altogether without changing the cost; it is the reduction used for the second kind of face in the proof of LEMMA II.
--
--   **Formalization Note** Here the original model has $m + 1$ variables (`Fin (m + 1) → ℝ`), and Lean's `j : Fin (m + 1)` is the paper's index $j$ = `j + 1`. Removing the variable is `Fin.removeNth`. No sign or domain hypothesis is needed (the page has none); the identity holds for every point satisfying $S_j = S_{j-1} + T_j$.
-- source:
--   Simpson, In-Process Inventories, Operations Research 6 (1958), p. 869, THEOREM II

import Mathlib
import Definitions.Def_SimpsonInv_Vertex_Setting

namespace SimpsonInv.Vertex

theorem theorem_II {m : ℕ} (c S0 Sn : ℝ) (r T : ℕ → ℝ) (S : Fin (m + 1) → ℝ) (j : Fin (m + 1))
    (hj : S j = extVec S0 Sn S j.val + T (j.val + 1)) :
    cost c r T S0 Sn S =
      cost c (coupledR r (j.val + 1)) (coupledT T (j.val + 1)) S0 Sn (Fin.removeNth j S) := by sorry

end SimpsonInv.Vertex
