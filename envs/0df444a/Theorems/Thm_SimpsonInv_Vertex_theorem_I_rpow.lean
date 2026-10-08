-- Prove2me | Theorems.Thm_SimpsonInv_Vertex_theorem_I_rpow
-- name    : SimpsonInv.Vertex.theorem_I_rpow
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:27:16.729581+00:00
-- url     : https://prove2.me/theorems/eb6c2f63-1fd5-4505-9aba-9c231a6abe0f
-- title:
--   Extension of the main theorem, p. 871 — with √· replaced by t^k, ½ ≤ k ≤ 1, the minimum still occurs at a vertex of D
-- statement:
--   Let $n = m + 1$, let $c, S_0, S_n, T_1, \dots, T_n$ be real constants, $r_1, \dots, r_n > 0$, and let $k$ be a constant with $\tfrac12 \le k \le 1$. Let $D$ be the domain of THEOREM I ($S_i \ge 0$ and $S_{i-1} - S_i + T_i \ge 0$) and assume $D \neq \emptyset$. Then the function
--   $$
--   f_k(S_1, \dots, S_{n-1}) = c + \sum_{i=1}^{n} r_i \,(S_{i-1} - S_i + T_i)^k
--   $$
--   attains its minimum over $D$ at a vertex of $D$.
--
--   This covers correlated demand, where the standard deviation of demand over a time $t$ grows like $t^k$ instead of $\sqrt t$; $k = 1$ is the linear-programming case.
--
--   **Formalization Note** Vertex means extreme point. $r_i > 0$ (equation (8)) and $D \ne \emptyset$ are added as for THEOREM I. The power is `Real.rpow`; on $D$ its base is nonnegative. The range $\tfrac12 \le k \le 1$ is the page's "between ½ and 1", endpoints included because the page treats $k = 1$ as the limiting case where "the result is known".
-- source:
--   Simpson, In-Process Inventories, Operations Research 6 (1958), p. 871, Extension of the main theorem, Correlated demand

import Mathlib
import Definitions.Def_SimpsonInv_Vertex_Setting

namespace SimpsonInv.Vertex

theorem theorem_I_rpow {m : ℕ} (k c S0 Sn : ℝ) (r T : ℕ → ℝ)
    (hk : 1 / 2 ≤ k) (hk1 : k ≤ 1)
    (hr : ∀ i ∈ Finset.Icc 1 (m + 1), 0 < r i)
    (hD : (dom (m := m) T S0 Sn).Nonempty) :
    ∃ v ∈ Set.extremePoints ℝ (dom (m := m) T S0 Sn),
      IsMinOn (costPow k c r T S0 Sn) (dom (m := m) T S0 Sn) v := by sorry

end SimpsonInv.Vertex
