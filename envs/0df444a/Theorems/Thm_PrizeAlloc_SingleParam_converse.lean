-- Prove2me | Theorems.Thm_PrizeAlloc_SingleParam_converse
-- name    : PrizeAlloc.SingleParam.converse
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:33:59.888882+00:00
-- url     : https://prove2.me/theorems/61d1e990-c547-4b56-9ffe-f94582c160dd
-- title:
--   Theorem 2, converse, p. 31 — every single-parametric rule satisfies anonymity, order preservation, winner strict endowment monotonicity and local consistency
-- statement:
--   Let $\varphi$ be a prize allocation rule that is single-parametric: for some continuous non-decreasing $f:\mathbb R_+\to\mathbb R_+$ with $f(x)\le x$, every competition $(N,\mathcal R,E)$ is allocated as $\varphi_i(N,\mathcal R,E)=f^{(\mathcal R(i)-1)}(x)$ with $\sum_{k=1}^{|N|}f^{(k-1)}(x)=E$. Then
--   $$\varphi \text{ satisfies anonymity, order preservation, winner strict endowment monotonicity and local consistency.}$$
--
--   This is the "if" direction of Theorem 2, which the paper calls readily checked.
--
--   **Formalization Note** The standing assumption that $U$ is countable with at least three elements is not needed and is omitted, which only strengthens the statement.
-- source:
--   Dietzenbacher and Kondratev, Fair and Consistent Prize Allocation in Competitions, arXiv:2008.08985v2, p. 31, proof of Theorem 2, first sentence

import Mathlib
import Definitions.Def_PrizeAlloc_SingleParam_Setting
import Definitions.Def_PrizeAlloc_SingleParam_Rules

namespace PrizeAlloc.SingleParam

theorem converse {U : Type*} [DecidableEq U]
    (φ : List U → ℝ → U → ℝ) (hφ : PrizeAlloc.Interval.IsPrizeRule φ) (h : IsSingleParamRule φ) :
    PrizeAlloc.Interval.Anonymous φ ∧ PrizeAlloc.Interval.OrderPreserving φ ∧ PrizeAlloc.Interval.WinnerStrictMonotone φ ∧ LocallyConsistent φ := by sorry

end PrizeAlloc.SingleParam
