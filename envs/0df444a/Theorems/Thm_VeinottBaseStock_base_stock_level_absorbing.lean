-- Prove2me | Theorems.Thm_VeinottBaseStock_base_stock_level_absorbing
-- name    : VeinottBaseStock.base_stock_level_absorbing
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:40:39.004996+00:00
-- url     : https://prove2.me/theorems/00358c04-5ace-4d05-b562-4be1b4536d79
-- title:
--   Proofs of Theorems 3.1–3.2, pp. 211, 215 — once the base stock level is attained, it is attained in every later period
-- statement:
--   Consider the inventory model under its standing assumptions, levels $\bar y_i$ satisfying (3b), and an initial vector $x_1 \in X_1$. Let $x_i^*, y_i^*$ be the inventories before and after ordering when the base stock policy is followed from $x_1$ along a demand path $t_1, t_2, \dots$ with $t_j \in \mathfrak{D}_j$ for all $j$. If in some period $k$
--   $$q_k(x_k^*) \le \bar y_k,$$
--   then
--   $$y_i^* = \bar y_i \qquad \text{for all } i \ge k.$$
--
--   With $k = 1$ this is the step of Theorem 3.1's proof; with $k = T$, the first period in which the base stock level is attainable, it is the step "for $i \ge T$, $y_i^* = \bar y_i$" in the proof of Theorem 3.2.
--
--   **Formalization Note.** Lean period $k$ is the paper's period $k+1$. The trajectory is the generic trajectory (`stateSeq`, `orderSeq`) of the base stock policy along the path `d`.
-- source:
--   Veinott, Optimal Policy for a Multi-Product, Dynamic, Nonstationary Inventory Problem, Management Science 12(3):206–222 (1965), p. 211 (proof of Theorem 3.1) and p. 215 (proof of Theorem 3.2)

import Mathlib
import Definitions.Def_VeinottBaseStock_Model
import Definitions.Def_VeinottBaseStock_BaseStock

open MeasureTheory ProbabilityTheory

namespace VeinottBaseStock

/-- Proofs of Theorems 3.1 (p. 211) and 3.2 (p. 215): under (3b), along every possible demand
path, once the base stock policy orders up to `ȳ_k` (because `q_k(x*_k) ≤ ȳ_k`) it orders up to
`ȳ_i` in every later period `i ≥ k`. -/
theorem base_stock_level_absorbing {n m : ℕ} (M : Model n m) (ybar : ℕ → Fin n → ℝ)
    (x₁ : Fin n → ℝ) (hM : M.Standing) (hx₁ : x₁ ∈ M.X 0) (h3b : M.H3b ybar)
    (d : ℕ → Fin m → ℝ) (hd : ∀ j, d j ∈ M.Dset j) (k : ℕ)
    (hk : M.q k (M.stateSeq (M.baseStock ybar x₁) x₁ d k) ≤ coeVec (ybar k)) :
    ∀ i, k ≤ i → M.orderSeq (M.baseStock ybar x₁) d i = ybar i := by sorry

end VeinottBaseStock
