-- Prove2me | Theorems.Thm_PrizeAlloc_SingleParam_theorem_2
-- name    : PrizeAlloc.SingleParam.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:34:33.690425+00:00
-- url     : https://prove2.me/theorems/31a0e42e-f566-4f0c-94a4-4adb13e7f747
-- title:
--   Theorem 2 — a prize allocation rule satisfies anonymity, order preservation, winner strict endowment monotonicity and local consistency iff it is a single-parametric rule
-- statement:
--   Let $U$ be a countable set of at least three potential competitors, and let $\varphi$ be a prize allocation rule on the competitions over $U$. Then
--   $$\varphi \text{ satisfies anonymity, order preservation, winner strict endowment monotonicity and local consistency} \iff \varphi \text{ is a single-parametric rule.}$$
--   That is, the four axioms hold exactly when there is a continuous, non-decreasing $f:\mathbb R_+\to\mathbb R_+$ with $f(x)\le x$ such that in each competition $(N,\mathcal R,E)$ the winner gets $x$, the competitor in position $k$ gets $f^{(k-1)}(x)$, and $x$ is chosen with $\sum_{k=1}^{|N|}f^{(k-1)}(x)=E$.
--
--   The theorem describes every rule with these fairness and consistency properties by a single function of one variable, the map from one position's prize to the next.
--
--   **Formalization Note** The standing assumptions of §2.1 ($U$ countable, at least three potential competitors) are hypotheses. Competitions are encoded as in the Setting item.
-- source:
--   Dietzenbacher and Kondratev, Fair and Consistent Prize Allocation in Competitions, arXiv:2008.08985v2, p. 18, Theorem 2 (proof pp. 31–32)

import Mathlib
import Definitions.Def_PrizeAlloc_SingleParam_Setting
import Definitions.Def_PrizeAlloc_SingleParam_Rules

namespace PrizeAlloc.SingleParam

theorem theorem_2 {U : Type*} [DecidableEq U] [Countable U]
    (hU : ∃ a b c : U, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (φ : List U → ℝ → U → ℝ) (hφ : PrizeAlloc.Interval.IsPrizeRule φ) :
    (PrizeAlloc.Interval.Anonymous φ ∧ PrizeAlloc.Interval.OrderPreserving φ ∧ PrizeAlloc.Interval.WinnerStrictMonotone φ ∧ LocallyConsistent φ) ↔
      IsSingleParamRule φ := by sorry

end PrizeAlloc.SingleParam
