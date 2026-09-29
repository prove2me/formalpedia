-- Prove2me | Theorems.Thm_VeinottBaseStock_base_stock_policy_optimal
-- name    : VeinottBaseStock.base_stock_policy_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:43:26.086114+00:00
-- url     : https://prove2.me/theorems/0baf579a-31a3-4b7d-94a5-e8023edf2c78
-- title:
--   Theorem 3.2 — the base stock ordering policy is optimal
-- statement:
--   Consider Veinott's multi-product, nonstationary, infinite-horizon inventory model under its standing assumptions, with independent demands $D_1, D_2, \dots$ and an initial inventory vector $x_1 \in X_1$. Suppose the levels $\bar y_1, \bar y_2, \dots$ satisfy
--
--   1. **(3a)** $\bar y_i \in Y_i$ minimizes $G_i(y)$ over $Y_i$;
--   2. **(3b)** $q_{i+1}(s_i(\bar y_i, t)) \le \bar y_{i+1}$ for all $t \in \mathfrak{D}_i$;
--   3. **(3c)** $Y_i$ is closed and linearly ordered by $\le$;
--   4. **(3d)** $G_i(y)$ and $s_i(y,t)$ ($t \in \mathfrak{D}_i$) are nondecreasing in $y$ on $\{y \in Y_i : y \ge \bar y_i\}$, and $q_i(x) \le q_i(x')$ whenever $x \le x'$ in $X_i$ and $q_i(x) \not\le \bar y_i$;
--
--   and that from every $x \in X_i$ some order $y \in Y_i$ with $y \ge q_i(x)$ is possible. Then the **base stock ordering policy**
--   $$\bar Y_i^*(H_i^*) = \begin{cases} \bar y_i, & q_i(x_i^*) \le \bar y_i, \\ w_i(x_i^*), & q_i(x_i^*) \not\le \bar y_i, \end{cases} \qquad (i = 1, 2, \dots),$$
--   where $x_i^*$ is the inventory before ordering in period $i$ when this policy is followed and $w_i(x)$ is the minimal element of $Y_i \cap \{y : y \ge q_i(x), y \ge \bar y_i\}$, is feasible and optimal: its expected discounted cost $f(x_1 \mid \bar Y^*) = \sum_i \beta_i E G_i(y_i^*)$ is at most that of every feasible ordering policy.
--
--   The theorem says that in this multi-product nonstationary model an optimal policy is myopic: in each period, order up to the one-period optimal level if possible, and otherwise order the least feasible amount. No dynamic programming recursion is needed to compute it.
--
--   **Formalization Note.** Lean period $k$ is the paper's period $k+1$. The printed theorem displays the policy's formula; its conclusion, as the proof says ("proving the optimality of $\bar Y^*$", p. 215), is that this policy is optimal, which includes its feasibility. Policies are functions of past demands (no loss of generality, p. 219). Two points differ from the page: (3d)'s $q$-clause is in the one-sided form used by the proof (the literal region-only reading makes the theorem false; see the moderation notes), and order feasibility (`hfeas`) is used by the paper without being stated (p. 212).
-- source:
--   Veinott, Optimal Policy for a Multi-Product, Dynamic, Nonstationary Inventory Problem, Management Science 12(3):206–222 (1965), p. 213, Theorem 3.2 (proof pp. 214–215)

import Mathlib
import Definitions.Def_VeinottBaseStock_Model
import Definitions.Def_VeinottBaseStock_BaseStock

open MeasureTheory ProbabilityTheory

namespace VeinottBaseStock

/-- Theorem 3.2 (p. 213): under (3a), (3b), (3c) and (3d), the base stock ordering policy — order
up to `ȳ_i` if `q_i(x*_i) ≤ ȳ_i`, otherwise up to `w_i(x*_i)` — is feasible and optimal. -/
theorem base_stock_policy_optimal {n m : ℕ} (M : Model n m) (ybar : ℕ → Fin n → ℝ)
    (x₁ : Fin n → ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℕ → Ω → Fin m → ℝ) (hM : M.Standing) (hD : M.IsDemandProcess P D)
    (hx₁ : x₁ ∈ M.X 0) (h3a : M.H3a ybar) (h3b : M.H3b ybar) (h3c : M.H3c) (h3d : M.H3d ybar)
    (hfeas : M.OrderFeasible) :
    M.IsOptimal x₁ P D (M.baseStock ybar x₁) := by sorry

end VeinottBaseStock
