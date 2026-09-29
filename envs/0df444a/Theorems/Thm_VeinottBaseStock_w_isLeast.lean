-- Prove2me | Theorems.Thm_VeinottBaseStock_w_isLeast
-- name    : VeinottBaseStock.w_isLeast
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:39:15.719054+00:00
-- url     : https://prove2.me/theorems/f3e176ea-cc5d-4d72-b18b-3f93ac79626d
-- title:
--   §3, p. 212 — $w_i(x)$ is the minimal element of $Y_i \cap \{y \ge q_i(x), y \ge \bar y_i\}$, and $w_i(x) = \bar y_i$ when $q_i(x) \le \bar y_i$
-- statement:
--   Consider the inventory model of the mission under its standing assumptions, with levels $\bar y_i$ satisfying (3a) ($\bar y_i \in Y_i$ minimizes $G_i$ over $Y_i$) and (3c) ($Y_i$ is closed and linearly ordered), and assume that for each $x \in X_i$ some $y \in Y_i$ satisfies $y \ge q_i(x)$. Then for every period $i$ and every $x \in X_i$:
--
--   1. $w_i(x)$ is the minimal element of the set
--   $$Y_i \cap \{ y : y \ge q_i(x),\ y \ge \bar y_i \};$$
--   2. if $q_i(x) \le \bar y_i$, then $w_i(x) = \bar y_i$.
--
--   This makes the base stock rule well defined: when the base stock level $\bar y_i$ cannot be attained, the minimal feasible level $w_i(x)$ exists.
--
--   **Formalization Note.** Lean period $k$ is the paper's period $k+1$. The hypothesis `hfeas : M.OrderFeasible` (some admissible order exists from every $x \in X_i$) is used by the paper without being stated: without it the set above may be empty.
-- source:
--   Veinott, Optimal Policy for a Multi-Product, Dynamic, Nonstationary Inventory Problem, Management Science 12(3):206–222 (1965), p. 212, §3 (definition of w_i(x) and the observation that w_i(x) = ȳ_i when q_i(x) ≤ ȳ_i)

import Mathlib
import Definitions.Def_VeinottBaseStock_Model
import Definitions.Def_VeinottBaseStock_BaseStock

open MeasureTheory ProbabilityTheory

namespace VeinottBaseStock

/-- §3, p. 212: under (3a) and (3c), for every `x ∈ X_i` the set
`Y_i ∩ {y | y ≥ q_i(x), y ≥ ȳ_i}` has the least element `w_i(x)`, and `w_i(x) = ȳ_i` whenever
`q_i(x) ≤ ȳ_i`. -/
theorem w_isLeast {n m : ℕ} (M : Model n m) (ybar : ℕ → Fin n → ℝ)
    (hM : M.Standing) (h3a : M.H3a ybar) (h3c : M.H3c) (hfeas : M.OrderFeasible)
    (k : ℕ) (x : Fin n → ℝ) (hx : x ∈ M.X k) :
    IsLeast (M.orderSet ybar k x) (M.w ybar k x) ∧
      (M.q k x ≤ coeVec (ybar k) → M.w ybar k x = ybar k) := by sorry

end VeinottBaseStock
