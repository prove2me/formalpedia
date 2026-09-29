-- Prove2me | Theorems.Thm_VeinottBaseStock_pathwise_G_dominance
-- name    : VeinottBaseStock.pathwise_G_dominance
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:42:08.057731+00:00
-- url     : https://prove2.me/theorems/0bf118d8-6190-4197-a6ca-4489446cb6a2
-- title:
--   Proof of Theorem 3.2, pp. 214–215 — $G_i(y_i^*) \le G_i(y_i)$ in every period, along every demand path
-- statement:
--   Consider the inventory model under its standing assumptions and hypotheses (3a)–(3d), assume that for each $x \in X_i$ some $y \in Y_i$ satisfies $y \ge q_i(x)$, and let $x_1 \in X_1$. Fix a demand path $t_1, t_2, \dots$ with $t_j \in \mathfrak{D}_j$, and let $y_i^*$ and $y_i$ be the inventories after ordering under the base stock policy and under an arbitrary feasible policy, both started from $x_1$. Then
--   $$G_i(y_i^*) \le G_i(y_i) \qquad \text{for every period } i.$$
--
--   The paper proves this separately for $i < T$ and for $i \ge T$; taking expectations and summing with the weights $\beta_i$ then gives the optimality of the base stock policy.
--
--   **Formalization Note.** Lean period $k$ is the paper's period $k+1$. (3d)'s $q$-clause is the one-sided form, and order feasibility is used by the paper without being stated.
-- source:
--   Veinott, Optimal Policy for a Multi-Product, Dynamic, Nonstationary Inventory Problem, Management Science 12(3):206–222 (1965), pp. 214–215, proof of Theorem 3.2

import Mathlib
import Definitions.Def_VeinottBaseStock_Model
import Definitions.Def_VeinottBaseStock_BaseStock

open MeasureTheory ProbabilityTheory

namespace VeinottBaseStock

/-- Proof of Theorem 3.2, pp. 214–215: along every possible demand path, the base stock policy
incurs no larger one-period expected cost than any feasible policy in every period:
`G_i(y*_i) ≤ G_i(y_i)`. -/
theorem pathwise_G_dominance {n m : ℕ} (M : Model n m) (ybar : ℕ → Fin n → ℝ) (x₁ : Fin n → ℝ)
    (hM : M.Standing) (hx₁ : x₁ ∈ M.X 0) (h3a : M.H3a ybar) (h3b : M.H3b ybar) (h3c : M.H3c)
    (h3d : M.H3d ybar) (hfeas : M.OrderFeasible)
    (Ŷ : Pol n m) (hŶ : M.Feasible x₁ Ŷ) (d : ℕ → Fin m → ℝ) (hd : ∀ j, d j ∈ M.Dset j) :
    ∀ k, M.G k (M.orderSeq (M.baseStock ybar x₁) d k) ≤ M.G k (M.orderSeq Ŷ d k) := by sorry

end VeinottBaseStock
