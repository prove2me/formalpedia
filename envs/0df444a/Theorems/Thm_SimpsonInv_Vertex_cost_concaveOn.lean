-- Prove2me | Theorems.Thm_SimpsonInv_Vertex_cost_concaveOn
-- name    : SimpsonInv.Vertex.cost_concaveOn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:26:37.263988+00:00
-- url     : https://prove2.me/theorems/cf373044-fb2b-47b6-a9a9-7c0f274f0b44
-- title:
--   The main theorem, p. 868 — the cost c + Σ rᵢ√(Sᵢ₋₁ − Sᵢ + Tᵢ) is concave on D
-- statement:
--   Let $n = m + 1$, let $c, S_0, S_n, T_1, \dots, T_n$ be real constants and $r_1, \dots, r_n \ge 0$. Then Simpson's cost function
--   $$
--   f(S_1, \dots, S_{n-1}) = c + \sum_{i=1}^{n} r_i \sqrt{S_{i-1} - S_i + T_i}
--   $$
--   is concave ("concave downward") on its domain $D$, the set of points with $S_i \ge 0$ for $1 \le i \le n-1$ and $S_{i-1} - S_i + T_i \ge 0$ for $1 \le i \le n$.
--
--   Concavity is the structural fact behind the paper's main theorem: a concave function on a polytope is minimized at a vertex.
--
--   **Formalization Note** The paper takes $r_i > 0$ (equation (8)); concavity needs only $r_i \ge 0$, so the hypothesis is the weaker one. Lean index $j$ of `Fin m → ℝ` is the paper's $S_{j+1}$.
-- source:
--   Simpson, In-Process Inventories, Operations Research 6 (1958), p. 868, The main theorem (first clause)

import Mathlib
import Definitions.Def_SimpsonInv_Vertex_Setting

namespace SimpsonInv.Vertex

theorem cost_concaveOn {m : ℕ} (c S0 Sn : ℝ) (r T : ℕ → ℝ)
    (hr : ∀ i ∈ Finset.Icc 1 (m + 1), 0 ≤ r i) :
    ConcaveOn ℝ (dom (m := m) T S0 Sn) (cost c r T S0 Sn) := by sorry

end SimpsonInv.Vertex
