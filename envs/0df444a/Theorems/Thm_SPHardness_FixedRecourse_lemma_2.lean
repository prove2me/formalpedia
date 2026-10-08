-- Prove2me | Theorems.Thm_SPHardness_FixedRecourse_lemma_2
-- name    : SPHardness.FixedRecourse.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:08:48.178533+00:00
-- url     : https://prove2.me/theorems/8a601dc9-1bc7-4739-81f2-43ed556e7fc5
-- title:
--   Lemma 2, p. 6 — derivative of expected recourse equals volume minus one
-- statement:
--   For $\alpha\in\mathbb R^k_+$ and $\beta\ge0$, except for the degenerate point $\alpha=0,\beta=0$, the expected recourse is differentiable with respect to its budget and
--   $$\frac{\partial\mathcal Q(\alpha,\beta)}{\partial\beta}=V(\alpha,\beta)-1.$$
--   This is the bridge from expected recourse to knapsack volume in Theorem 1.
--
--   **Formalization Note** At $\alpha=0,\beta=0$, $\mathcal Q(0,\beta)=\max\{-\beta,0\}$ has no derivative; the paper's unrestricted statement needs this exclusion.
-- source:
--   Hanasusanto, Kuhn & Wiesemann, A comment on "computational complexity of stochastic programming problems", Optimization Online preprint 2015/03/4825 (version of October 6, 2015), p. 6, Lemma 2

import Mathlib
import Definitions.Def_SPHardness_FixedRecourse_Model

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace SPHardness.FixedRecourse

theorem lemma_2 {k : ℕ} (α : Fin k → ℝ) (β : ℝ)
    (hα : ∀ j, 0 ≤ α j) (hβ : 0 ≤ β)
    (hnontrivial : (∃ j, 0 < α j) ∨ 0 < β) :
    HasDerivAt (fun t => expRecourse α t) (vol α β - 1) β := by sorry
end SPHardness.FixedRecourse
