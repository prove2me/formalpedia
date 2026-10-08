-- Prove2me | Theorems.Thm_SimpsonInv_Vertex_theorem_I
-- name    : SimpsonInv.Vertex.theorem_I
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:27:22.823774+00:00
-- url     : https://prove2.me/theorems/e051876e-295b-46b9-b906-68a8c45bea3a
-- title:
--   THEOREM I, p. 869 — the minimum of c + Σ rᵢ√(Sᵢ₋₁ − Sᵢ + Tᵢ) over D occurs at a vertex of D
-- statement:
--   Let $n = m + 1$ be the number of operations, and let $c$, $S_0$, $S_n$, $T_1, \dots, T_n$ be real constants and $r_1, \dots, r_n > 0$. Consider the function of the $n - 1$ real variables $S_1, \dots, S_{n-1}$
--   $$
--   f(S_1, \dots, S_{n-1}) = c + \sum_{i=1}^{n} r_i \sqrt{S_{i-1} - S_i + T_i},
--   $$
--   on the domain $D$ of points at which every variable is nonnegative, $S_i \ge 0$, and every radicand is nonnegative, $S_{i-1} - S_i + T_i \ge 0$. If $D$ is nonempty, then $f$ attains its minimum over $D$ at a vertex of $D$: there is an extreme point $v$ of $D$ with
--   $$
--   f(v) \le f(S) \quad \text{for all } S \in D.
--   $$
--
--   In Simpson's base-stock model the variables are the service times quoted between consecutive operations and $f$ is the total cost of in-process and finished-goods inventories; the theorem reduces the choice of a cheapest mode of operation from a continuum to the finitely many vertices of $D$.
--
--   **Formalization Note** "Vertex" is an extreme point of $D$ (`Set.extremePoints ℝ D`); for a polyhedron these coincide. Two hypotheses are added and disclosed: $r_i > 0$, from equation (8), without which the statement is false (with $n = 2$, $r_1 = r_2 = -1$, $S_0 = 0$, $S_2 = 1$, $T_1 = 2$, $T_2 = 1$, the only minimizer on $D = [0,2]$ is $S_1 = 1$); and $D \ne \emptyset$, which "the minimum occurs" presupposes. The page's "$n-1$-dimensional polyhedron" is not imposed as a hypothesis; the conclusion is stated for every nonempty $D$. With $m = n - 1$ variables a point is `Fin m → ℝ`, and Lean index $j$ is the paper's $S_{j+1}$.
-- source:
--   Simpson, In-Process Inventories, Operations Research 6 (1958), p. 869, THEOREM I

import Mathlib
import Definitions.Def_SimpsonInv_Vertex_Setting

namespace SimpsonInv.Vertex

theorem theorem_I {m : ℕ} (c S0 Sn : ℝ) (r T : ℕ → ℝ)
    (hr : ∀ i ∈ Finset.Icc 1 (m + 1), 0 < r i)
    (hD : (dom (m := m) T S0 Sn).Nonempty) :
    ∃ v ∈ Set.extremePoints ℝ (dom (m := m) T S0 Sn),
      IsMinOn (cost c r T S0 Sn) (dom (m := m) T S0 Sn) v := by sorry

end SimpsonInv.Vertex
