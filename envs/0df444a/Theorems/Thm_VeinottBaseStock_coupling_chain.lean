-- Prove2me | Theorems.Thm_VeinottBaseStock_coupling_chain
-- name    : VeinottBaseStock.coupling_chain
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:41:40.615684+00:00
-- url     : https://prove2.me/theorems/0ac595e5-a650-4fab-8605-5fd764e1d96c
-- title:
--   Eq. (3.1), p. 214 — $\bar y_i < y_i^* = w_i(x_i^*) \le w_i(x_i) \le y_i$ before the base stock level is attained
-- statement:
--   Consider the inventory model under its standing assumptions and hypotheses (3a)–(3d), assume that for each $x \in X_i$ some $y \in Y_i$ satisfies $y \ge q_i(x)$, and let $x_1 \in X_1$. Fix a demand path $t_1, t_2, \dots$ with $t_j \in \mathfrak{D}_j$. Let $x_i^*, y_i^*$ be the inventories before and after ordering under the base stock policy, and $x_i, y_i$ those under an arbitrary feasible policy $\bar Y$, both started from $x_1$ and driven by the same demands. If $k$ is a period such that $q_j(x_j^*) \not\le \bar y_j$ for every $j \le k$ (that is, $k < T$, where $T$ is the first period with $q_T(x_T^*) \le \bar y_T$), then
--   $$\bar y_k < y_k^* = w_k(x_k^*) \le w_k(x_k) \le y_k. \tag{3.1}$$
--
--   This coupling says that until the base stock level becomes attainable, the base stock policy holds less stock after ordering than any feasible policy, while staying at or above $\bar y_k$.
--
--   **Formalization Note.** Lean period $k$ is the paper's period $k+1$. The strict inequality $\bar y_k < y_k^*$ is the paper's $>$ of footnote 3 ($u > v$ iff $u \ge v$ and $u \ne v$), which is Lean's `<` on `Fin n → ℝ`. The period $T$ (possibly $+\infty$) is encoded by the prefix condition `hbefore`. (3d)'s $q$-clause is the one-sided form, and order feasibility is used by the paper without being stated.
-- source:
--   Veinott, Optimal Policy for a Multi-Product, Dynamic, Nonstationary Inventory Problem, Management Science 12(3):206–222 (1965), p. 214, proof of Theorem 3.2, eq. (3.1)

import Mathlib
import Definitions.Def_VeinottBaseStock_Model
import Definitions.Def_VeinottBaseStock_BaseStock

open MeasureTheory ProbabilityTheory

namespace VeinottBaseStock

/-- (3.1), p. 214: let `x*, y*` be the base stock trajectory and `x, y` the trajectory of an
arbitrary feasible policy from the same `x_1` along the same possible demand path. For every
period `k` before the first period `T` with `q_T(x*_T) ≤ ȳ_T`,
`ȳ_k < y*_k = w_k(x*_k) ≤ w_k(x_k) ≤ y_k`. -/
theorem coupling_chain {n m : ℕ} (M : Model n m) (ybar : ℕ → Fin n → ℝ) (x₁ : Fin n → ℝ)
    (hM : M.Standing) (hx₁ : x₁ ∈ M.X 0) (h3a : M.H3a ybar) (h3b : M.H3b ybar) (h3c : M.H3c)
    (h3d : M.H3d ybar) (hfeas : M.OrderFeasible)
    (Ŷ : Pol n m) (hŶ : M.Feasible x₁ Ŷ) (d : ℕ → Fin m → ℝ) (hd : ∀ j, d j ∈ M.Dset j)
    (k : ℕ)
    (hbefore : ∀ j ≤ k, ¬ M.q j (M.stateSeq (M.baseStock ybar x₁) x₁ d j) ≤ coeVec (ybar j)) :
    ybar k < M.orderSeq (M.baseStock ybar x₁) d k ∧
      M.orderSeq (M.baseStock ybar x₁) d k =
        M.w ybar k (M.stateSeq (M.baseStock ybar x₁) x₁ d k) ∧
      M.w ybar k (M.stateSeq (M.baseStock ybar x₁) x₁ d k) ≤
        M.w ybar k (M.stateSeq Ŷ x₁ d k) ∧
      M.w ybar k (M.stateSeq Ŷ x₁ d k) ≤ M.orderSeq Ŷ d k := by sorry

end VeinottBaseStock
