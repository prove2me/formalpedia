-- Prove2me | Theorems.Thm_RegLearnGames_FirstOrder_smoothness_step
-- name    : RegLearnGames.FirstOrder.smoothness_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:45:39.829564+00:00
-- url     : https://prove2.me/theorems/ef743c56-6ebc-4c78-ae9c-b4ab5c052f66
-- title:
--   Smoothness step, supp. p. 10 — expected deviation cost is at most λOPT′ + µC(w)
-- statement:
--   Let $s^*$ witness $(\lambda,\mu)$-smoothness: for every pure profile $s$, the sum of costs incurred by players who each unilaterally switch to $s_i^*$ is at most $\lambda\mathrm{OPT}'+\mu C(s)$. For every mixed profile $w$,
--   $$\sum_i c_{i,s_i^*}(w)\le\lambda\mathrm{OPT}'+\mu C(w).$$
--
--   This transfers the pure-profile smoothness inequality to the independent mixed play generated during learning.
--
--   **Formalization Note** The Lean statement takes the explicit witness condition from equation (20), rather than an arbitrary unrelated profile. No sign assumptions on $\lambda$ or $\mu$ are needed for this expectation step.
-- source:
--   Syrgkanis, Agarwal, Luo, Schapire, Fast Convergence of Regularized Learning in Games, arXiv:1507.00407v5, supp. p. 10 (PDF p. 19), display after equation (22), beginning ‘By the smoothness assumption’

import Mathlib
import Definitions.Def_RegLearnGames_FirstOrder_Setting

namespace RegLearnGames.FirstOrder

open Finset

/-- Expected unilateral deviation costs are bounded by smoothness. -/
theorem smoothness_step {n d : ℕ} [NeZero d]
    (c : Fin n → (Fin n → Fin d) → ℝ)
    (w : Fin n → Fin d → ℝ) (hw : AGT.IsMixedProfile w)
    (lam mu : ℝ) (sstar : Fin n → Fin d)
    (hsmooth : ∀ s : Fin n → Fin d,
      (∑ i, c i (Function.update s i (sstar i))) ≤
        lam * optCost c + mu * socialCostPure c s) :
    (∑ i, costVec c w i (sstar i)) ≤
      lam * optCost c + mu * socialCost c w := by sorry

end RegLearnGames.FirstOrder
