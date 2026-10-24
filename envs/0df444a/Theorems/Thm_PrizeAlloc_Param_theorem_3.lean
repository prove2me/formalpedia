-- Prove2me | Theorems.Thm_PrizeAlloc_Param_theorem_3
-- name    : PrizeAlloc.Param.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:34:01.000059+00:00
-- url     : https://prove2.me/theorems/9ff3803b-540e-4385-9aaf-a544c1788235
-- title:
--   Theorem 3 — a prize allocation rule satisfies anonymity, order preservation, winner strict endowment monotonicity and top consistency iff it is a parametric rule
-- statement:
--   Let $U$ be a countable set of at least three potential competitors and let $\varphi$ be a prize allocation rule on competitions $(N,\mathcal R,E)$ with $N\subseteq U$ finite, $\mathcal R$ a ranking of $N$ and $E\ge 0$. Then $\varphi$ satisfies
--
--   1. anonymity,
--   2. order preservation,
--   3. winner strict endowment monotonicity, and
--   4. top consistency
--
--   if and only if $\varphi$ is a **parametric rule**: there exist continuous, non-decreasing $f_1,f_2,\dots:\mathbb R_+\to\mathbb R_+$ with $f_1(x)=x$ and $f_{k+1}(x)\le f_k(x)$ for each $k$ and $x$, such that for each competition and each $i\in N$
--
--   $$\varphi_i(N,\mathcal R,E)=f_{\mathcal R(i)}(x),\qquad\text{where } \sum_{k=1}^{|N|}f_k(x)=E .$$
--
--   The theorem describes every rule that is fair in the anonymous, order-preserving sense, rewards the winner strictly for a larger endowment, and is invariant when the top segment of the ranking is put in a separate league: such a rule is determined by one function per position, of the winner's prize $x$.
--
--   **Formalization Note** Competitions are encoded as duplicate-free nonempty lists of elements of $U$ (best first) with the endowment $E\ge0$; positions are 1-based. The paper's standing assumptions that $U$ is countable and has at least three elements are hypotheses. The rule is a real-valued function whose values matter only on the domain of competitions. The representation is indexed from 1 ($f_0$ unused), and its properties hold on $\mathbb R_+$.
-- source:
--   Dietzenbacher and Kondratev, Fair and Consistent Prize Allocation in Competitions, arXiv:2008.08985v2, p. 22, Theorem 3 (proof pp. 32–33)

import Mathlib
import Definitions.Def_PrizeAlloc_Param_Setting
import Definitions.Def_PrizeAlloc_Param_ParametricRule

namespace PrizeAlloc.Param

/-- Theorem 3 (p. 22): a prize allocation rule satisfies anonymity, order preservation,
winner strict endowment monotonicity and top consistency iff it is a parametric rule. -/
theorem theorem_3 {U : Type*} [DecidableEq U] [Countable U]
    (hU : ∃ a b c : U, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (φ : List U → ℝ → U → ℝ) (hφ : PrizeAlloc.Interval.IsPrizeRule φ) :
    (PrizeAlloc.Interval.Anonymous φ ∧ PrizeAlloc.Interval.OrderPreserving φ ∧ PrizeAlloc.Interval.WinnerStrictMonotone φ ∧ TopConsistent φ) ↔
      IsParamRule φ := by sorry

end PrizeAlloc.Param
