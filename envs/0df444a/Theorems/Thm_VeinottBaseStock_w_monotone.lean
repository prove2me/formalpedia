-- Prove2me | Theorems.Thm_VeinottBaseStock_w_monotone
-- name    : VeinottBaseStock.w_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:40:02.667301+00:00
-- url     : https://prove2.me/theorems/065e472f-edc4-4500-86dd-daf74c195d5b
-- title:
--   Proof of Theorem 3.2, p. 214 — $w_i(x)$ is nondecreasing in $x$ where $q_i(x) \not\le \bar y_i$
-- statement:
--   Consider the inventory model under its standing assumptions and hypotheses (3a), (3c) and (3d), and assume that for each $x \in X_i$ some $y \in Y_i$ satisfies $y \ge q_i(x)$. Let $x, x' \in X_i$ with $x \le x'$ and $q_i(x) \not\le \bar y_i$. Then
--   $$w_i(x) \le w_i(x').$$
--
--   In the proof of Theorem 3.2 this transfers the monotonicity of the constraint $q_i$ to the minimal feasible order level, and is what lets a larger inventory under an arbitrary policy force a larger order level than the base stock policy's.
--
--   **Formalization Note.** Lean period $k$ is the paper's period $k+1$. (3d)'s $q$-clause is the one-sided form ($x \le x'$ and $q_i(x) \not\le \bar y_i$ imply $q_i(x) \le q_i(x')$), which is what this step of the paper uses. Order feasibility (`hfeas`) is used by the paper without being stated.
-- source:
--   Veinott, Optimal Policy for a Multi-Product, Dynamic, Nonstationary Inventory Problem, Management Science 12(3):206–222 (1965), p. 214, proof of Theorem 3.2

import Mathlib
import Definitions.Def_VeinottBaseStock_Model
import Definitions.Def_VeinottBaseStock_BaseStock

open MeasureTheory ProbabilityTheory

namespace VeinottBaseStock

/-- Proof of Theorem 3.2, p. 214: since `q_i(x)` is nondecreasing in `x` where
`q_i(x) ≰ ȳ_i`, so is `w_i(x)`. -/
theorem w_monotone {n m : ℕ} (M : Model n m) (ybar : ℕ → Fin n → ℝ)
    (hM : M.Standing) (h3a : M.H3a ybar) (h3c : M.H3c) (h3d : M.H3d ybar)
    (hfeas : M.OrderFeasible) (k : ℕ) (x x' : Fin n → ℝ) (hx : x ∈ M.X k) (hx' : x' ∈ M.X k)
    (hle : x ≤ x') (hq : ¬ M.q k x ≤ coeVec (ybar k)) :
    M.w ybar k x ≤ M.w ybar k x' := by sorry

end VeinottBaseStock
