-- Prove2me | Theorems.Thm_PooledRationing_AsymFeas_claim_22
-- name    : PooledRationing.AsymFeas.claim_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:31:33.425445+00:00
-- url     : https://prove2.me/theorems/c26c0e3b-2f2a-4011-811e-d3784e7d0cc6
-- title:
--   Equation (22) — simplex inequalities give individual service bounds
-- statement:
--   Let $\lambda_\varepsilon$ be a randomized policy satisfying equation (21): every nonnegative weight vector whose coordinates sum to at most one assigns a weighted service shortfall of at most $\varepsilon>0$. Then every customer meets its target to within $\varepsilon$:
--   $$
--   S_j(\lambda_\varepsilon)\ge\beta_j-\varepsilon\qquad\text{for every }j.
--   $$
--   This extracts the individual service conclusion from the minimax statement.
--
--   **Formalization Note** The randomized policy is a finite mixture of measurable deterministic policies. Customers and resources are indexed from zero. No integrability assumption is needed for this algebraic implication because its premise already concerns the defined real service values.
-- source:
--   Jiang, Wang & Zhang, Achieving High Individual Service-Levels without Safety Stock? Optimal Rationing Policy of Pooled Resources, SSRN 3385089 (version of 31 July 2021), pp. 13–14, (21)–(22) and proof

import Mathlib
import Definitions.Def_PooledRationing_AsymFeas_Setting

namespace PooledRationing.AsymFeas

open MeasureTheory

/-- Equation (22) from equation (21), pp. 13–14. -/
theorem claim_22 {n m : ℕ} (F : Measure (Fin n → ℝ)) [IsProbabilityMeasure F]
    (P : (Fin m → ℝ) → (Fin n → ℝ) → Set (Sol n m)) (c : Fin m → ℝ)
    (R : Fin n → ℝ → ℝ → ℝ) (β : Fin n → ℝ)
    (ε : ℝ) (hε : 0 < ε) (lam : RandPolicy P c)
    (h21 : ∀ w : Fin n → ℝ, 0 ≤ w → (∑ j, w j) ≤ 1 →
      ∑ j, w j * (β j - service F R lam j) ≤ ε) :
    ∀ j, β j - ε ≤ service F R lam j := by sorry

end PooledRationing.AsymFeas
