-- Prove2me | Theorems.Thm_VeinottBaseStock_const_base_stock_optimal
-- name    : VeinottBaseStock.const_base_stock_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:41:07.504987+00:00
-- url     : https://prove2.me/theorems/88422e34-0565-4afe-98de-699dcdd19712
-- title:
--   Theorem 3.1 — if $q_1(x_1) \le \bar y_1$, ordering up to $\bar y_i$ in every period is optimal
-- statement:
--   Consider the inventory model under its standing assumptions, with independent demands $D_1, D_2, \dots$, and levels $\bar y_i$ satisfying
--
--   1. **(3a)** $\bar y_i \in Y_i$ minimizes $G_i(y)$ over $Y_i$, for every $i$;
--   2. **(3b)** $q_{i+1}(s_i(\bar y_i, t)) \le \bar y_{i+1}$ for all $t \in \mathfrak{D}_i$ and every $i$.
--
--   Let $x_1 \in X_1$ with $q_1(x_1) \le \bar y_1$. Then the policy $\bar Y^*$ that orders up to $\bar y_i$ in every period, $\bar Y_i^* = \bar y_i$, is feasible and optimal, and its cost is
--   $$f(x_1 \mid \bar Y^*) = \sum_{i=1}^{\infty} \beta_i\, G_i(\bar y_i).$$
--
--   The theorem solves the problem when the initial inventory is small enough that the myopic levels $\bar y_i$ can be reached from the start, and it is the first case of the proof of Theorem 3.2.
--
--   **Formalization Note.** Lean period $k$ is the paper's period $k+1$. The series $\sum_i \beta_i G_i(\bar y_i)$ is written in the same encoding as the cost: $\sum_i \beta_i (G_i(\bar y_i) - \gamma_i) \in [0,\infty]$ plus the finite real $\sum_i \beta_i \gamma_i$, so a value of $+\infty$ is allowed.
-- source:
--   Veinott, Optimal Policy for a Multi-Product, Dynamic, Nonstationary Inventory Problem, Management Science 12(3):206–222 (1965), p. 211, Theorem 3.1

import Mathlib
import Definitions.Def_VeinottBaseStock_Model
import Definitions.Def_VeinottBaseStock_BaseStock

open MeasureTheory ProbabilityTheory

namespace VeinottBaseStock

/-- Theorem 3.1 (p. 211): under (3a) and (3b), if `q_1(x_1) ≤ ȳ_1` then the policy that orders up
to `ȳ_i` in every period is optimal, and its cost is `∑_i β_i G_i(ȳ_i)`. -/
theorem const_base_stock_optimal {n m : ℕ} (M : Model n m) (ybar : ℕ → Fin n → ℝ)
    (x₁ : Fin n → ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℕ → Ω → Fin m → ℝ) (hM : M.Standing) (hD : M.IsDemandProcess P D)
    (hx₁ : x₁ ∈ M.X 0) (h3a : M.H3a ybar) (h3b : M.H3b ybar)
    (hq : M.q 0 x₁ ≤ coeVec (ybar 0)) :
    M.IsOptimal x₁ P D (fun k _ => ybar k) ∧
      M.cost P D (fun k _ => ybar k) =
        (((∑' k, ENNReal.ofReal (M.β k * (M.G k (ybar k) - M.γ k)) : ENNReal)) : EReal) +
          ((∑' k, M.β k * M.γ k : ℝ) : EReal) := by sorry

end VeinottBaseStock
