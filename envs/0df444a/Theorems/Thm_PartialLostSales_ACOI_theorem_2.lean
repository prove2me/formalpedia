-- Prove2me | Theorems.Thm_PartialLostSales_ACOI_theorem_2
-- name    : PartialLostSales.ACOI.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:40:15.10984+00:00
-- url     : https://prove2.me/theorems/4fd1b618-fe63-4d50-b0a1-7f05155c8caa
-- title:
--   Theorem 2, p. 13 — Assumption B(ii) holds for the lost-sales COMDP: sup_{α∈[α∗,1)} u_α(z) < ∞ for every belief z
-- statement:
--   Consider the COMDP of the lost-sales inventory model observed only at zero, under the standing assumptions. Let $u_\alpha=v_\alpha-m_\alpha$ be its relative discounted value function. Then Assumption B(ii) holds: there is $\alpha_*\in(0,1)$ such that
--   $$\sup_{\alpha\in[\alpha_*,1)}u_\alpha(z)<\infty\qquad\text{for every belief }z\text{ with finite second moment.}$$
--
--   Theorem 2 is the main technical result of the paper. With (W*) and Lemma 3 it verifies the hypotheses of Lemma 2, which gives Theorem 1.
--
--   **Formalization Note.** The constant $\alpha_*$ is chosen before the belief $z$. The bound on $u_\alpha(z)$ may depend on $z$. The state space consists of beliefs with finite second moment, so "for all $z$ with a finite second moment" is "for all states". $u_\alpha$ uses truncated subtraction, which is exact here since $m_\alpha<\infty$.
-- source:
--   Bai, Chen & Stolyar, Average Cost Optimality in Partially Observed Lost-Sales Inventory Systems, SSRN preprint 3865728, p. 13, Theorem 2

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_PartialLostSales_ACOI_Model

open MeasureTheory ProbabilityTheory Filter Topology FeinbergLiang.ACOE
open scoped ENNReal NNReal

namespace PartialLostSales.ACOI

/-- Theorem 2, p. 13: Assumption B(ii) holds for the COMDP: there is `α* ∈ (0, 1)` with
`sup_{α ∈ [α*, 1)} u_α(z) < ∞` for every belief `z` with finite second moment. -/
theorem theorem_2 (P : Params) (hP : Standing P) (M : MDP (Bel P) (Act P))
    (hM : IsCOMDP P M) :
    ∃ αstar ∈ Set.Ioo (0 : ℝ) 1, ∀ z : Bel P,
      (⨆ α ∈ Set.Ico αstar 1, uRel M α z) ≠ ⊤ := by sorry

end PartialLostSales.ACOI
