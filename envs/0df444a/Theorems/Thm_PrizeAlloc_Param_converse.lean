-- Prove2me | Theorems.Thm_PrizeAlloc_Param_converse
-- name    : PrizeAlloc.Param.converse
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:33:52.867679+00:00
-- url     : https://prove2.me/theorems/d94521e1-205c-4ac5-b4e7-3fcda73fa599
-- title:
--   Proof of Theorem 3, p. 32 — every parametric rule satisfies anonymity, order preservation, winner strict endowment monotonicity and top consistency
-- statement:
--   Let $\varphi$ be a prize allocation rule on competitions over a set $U$ of potential competitors. If $\varphi$ is a parametric rule, that is, there are continuous non-decreasing $f_1,f_2,\dots:\mathbb R_+\to\mathbb R_+$ with $f_1(x)=x$ and $f_{k+1}\le f_k$ such that
--
--   $$\varphi_i(N,\mathcal R,E)=f_{\mathcal R(i)}(x),\qquad \sum_{k=1}^{|N|}f_k(x)=E,$$
--
--   then $\varphi$ satisfies
--
--   1. anonymity,
--   2. order preservation,
--   3. winner strict endowment monotonicity, and
--   4. top consistency.
--
--   This is the "if" direction of Theorem 3, which the paper calls readily checked.
--
--   **Formalization Note** No assumption on the size of $U$ is needed for this direction, so the standing hypotheses that $U$ is countable with at least three elements are omitted; this only strengthens the statement.
-- source:
--   Dietzenbacher and Kondratev, Fair and Consistent Prize Allocation in Competitions, arXiv:2008.08985v2, p. 32, proof of Theorem 3, first sentence

import Mathlib
import Definitions.Def_PrizeAlloc_Param_Setting
import Definitions.Def_PrizeAlloc_Param_ParametricRule

namespace PrizeAlloc.Param

/-- Proof of Theorem 3, first sentence (p. 32): every parametric rule satisfies anonymity,
order preservation, winner strict endowment monotonicity and top consistency. -/
theorem converse {U : Type*} [DecidableEq U]
    (φ : List U → ℝ → U → ℝ) (hφ : PrizeAlloc.Interval.IsPrizeRule φ) (hpar : IsParamRule φ) :
    PrizeAlloc.Interval.Anonymous φ ∧ PrizeAlloc.Interval.OrderPreserving φ ∧ PrizeAlloc.Interval.WinnerStrictMonotone φ ∧ TopConsistent φ := by sorry

end PrizeAlloc.Param
