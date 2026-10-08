-- Prove2me | Theorems.Thm_SPHardness_FixedRecourse_vol_lipschitz
-- name    : SPHardness.FixedRecourse.vol_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:08:39.004162+00:00
-- url     : https://prove2.me/theorems/1b8ed142-7549-423e-9ea7-4d4f3047dca1
-- title:
--   Proof of Theorem 1, p. 8 — volume growth bound from the last weight
-- statement:
--   Let $k\ge1$, $\alpha\in\mathbb R^k_+$, and let the final weight $\alpha_k$ be positive. For all real budgets $\beta\le\beta'$, knapsack volume is nondecreasing and
--   $$0\le V(\alpha,\beta')-V(\alpha,\beta)\le\frac{\beta'-\beta}{\alpha_k}.$$
--   This is the global volume-growth bound used by the finite-difference estimate.
--
--   **Formalization Note** The page writes $0\le\mathcal Q''\le1/\alpha_k$ and takes a supremum over $[0,h]$ in a calculation centered at $\beta$. The Lipschitz form also covers budgets at which the second derivative does not exist.
-- source:
--   Hanasusanto, Kuhn & Wiesemann, A comment on "computational complexity of stochastic programming problems", Optimization Online preprint 2015/03/4825 (version of October 6, 2015), p. 8, Q″ derivation in proof of Theorem 1

import Mathlib
import Definitions.Def_SPHardness_FixedRecourse_Model

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace SPHardness.FixedRecourse

theorem vol_lipschitz {k : ℕ} (hk : 0 < k) (α : Fin k → ℝ)
    (hα : ∀ j, 0 ≤ α j) (hαk : 0 < lastWeight hk α) :
    ∀ β β' : ℝ, β ≤ β' →
      0 ≤ vol α β' - vol α β ∧
      vol α β' - vol α β ≤ (β' - β) / lastWeight hk α := by sorry
end SPHardness.FixedRecourse
