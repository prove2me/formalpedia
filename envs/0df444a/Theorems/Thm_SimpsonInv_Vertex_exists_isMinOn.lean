-- Prove2me | Theorems.Thm_SimpsonInv_Vertex_exists_isMinOn
-- name    : SimpsonInv.Vertex.exists_isMinOn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:26:45.785741+00:00
-- url     : https://prove2.me/theorems/c849835a-d001-4f34-b28d-1e3b1eea59b4
-- title:
--   Appendix, p. 872 — f is continuous and D compact, so f achieves its minimum on D
-- statement:
--   Let $n = m + 1$, let $c, S_0, S_n$ and $r_i, T_i$ ($1 \le i \le n$) be real constants, and suppose the domain $D$ (all $S_i \ge 0$ and all radicands $S_{i-1} - S_i + T_i \ge 0$) is nonempty. Then the cost function
--   $$
--   f(S_1, \dots, S_{n-1}) = c + \sum_{i=1}^{n} r_i \sqrt{S_{i-1} - S_i + T_i}
--   $$
--   attains its minimum on $D$: there is $v \in D$ with $f(v) \le f(S)$ for every $S \in D$.
--
--   This is the first step of the Appendix's proof of THEOREM I; the rest of the proof locates the minimizer.
--
--   **Formalization Note** The nonemptiness of $D$ is added: "the function does achieve its minimum" presupposes it. No sign condition on $r_i$ is needed. Lean index $j$ of `Fin m → ℝ` is the paper's $S_{j+1}$.
-- source:
--   Simpson, In-Process Inventories, Operations Research 6 (1958), p. 872, Appendix. Proof of Theorem I (opening paragraph)

import Mathlib
import Definitions.Def_SimpsonInv_Vertex_Setting

namespace SimpsonInv.Vertex

theorem exists_isMinOn {m : ℕ} (c S0 Sn : ℝ) (r T : ℕ → ℝ)
    (hD : (dom (m := m) T S0 Sn).Nonempty) :
    ∃ v ∈ dom (m := m) T S0 Sn, IsMinOn (cost c r T S0 Sn) (dom (m := m) T S0 Sn) v := by sorry

end SimpsonInv.Vertex
