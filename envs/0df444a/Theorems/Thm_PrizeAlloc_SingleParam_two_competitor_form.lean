-- Prove2me | Theorems.Thm_PrizeAlloc_SingleParam_two_competitor_form
-- name    : PrizeAlloc.SingleParam.two_competitor_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:34:21.704168+00:00
-- url     : https://prove2.me/theorems/afcb35b6-ebd3-4080-9e75-41b57c1e8da5
-- title:
--   p. 31 — by anonymity the rule is single-parametric on all two-competitor competitions
-- statement:
--   Let $\varphi$ be a prize allocation rule satisfying anonymity, order preservation, winner strict endowment monotonicity and endowment continuity. Then there is a continuous, non-decreasing $f:\mathbb R_+\to\mathbb R_+$ with $f(x)\le x$ such that $\varphi$ is the single-parametric rule with representation $f$ on every competition with two competitors: for each $(N,\mathcal R,E)$ with $|N|=2$ there is $x\ge0$ with
--   $$x+f(x)=E,\qquad \varphi_i(N,\mathcal R,E)=x\ \text{ if }\mathcal R(i)=1,\qquad \varphi_i(N,\mathcal R,E)=f(x)\ \text{ if }\mathcal R(i)=2.$$
--
--   This is the base of the uniqueness argument for Theorem 2.
--
--   **Formalization Note** The statement is written in the general form $\sum_{k=0}^{|N|-1}f^{[k]}(x)=E$, $\varphi_i=f^{[\mathcal R(i)-1]}(x)$ restricted to rankings of length $2$. Endowment continuity is a hypothesis (Lemma 1 of the paper derives it from endowment monotonicity). The standing assumption that $U$ is countable with at least three elements is not needed and is omitted, which only strengthens the statement.
-- source:
--   Dietzenbacher and Kondratev, Fair and Consistent Prize Allocation in Competitions, arXiv:2008.08985v2, p. 31, proof of Theorem 2

import Mathlib
import Definitions.Def_PrizeAlloc_SingleParam_Setting
import Definitions.Def_PrizeAlloc_SingleParam_Rules

namespace PrizeAlloc.SingleParam

theorem two_competitor_form {U : Type*} [DecidableEq U]
    (φ : List U → ℝ → U → ℝ) (hφ : PrizeAlloc.Interval.IsPrizeRule φ) (hA : PrizeAlloc.Interval.Anonymous φ) (hOP : PrizeAlloc.Interval.OrderPreserving φ)
    (hW : PrizeAlloc.Interval.WinnerStrictMonotone φ) (hC : PrizeAlloc.Interval.EndowmentContinuous φ) :
    ∃ f : ℝ → ℝ, IsRepresentation f ∧
      ∀ l E, PrizeAlloc.Interval.IsRanking l → l.length = 2 → 0 ≤ E →
        ∃ x, 0 ≤ x ∧ (∑ k ∈ Finset.range l.length, f^[k] x) = E ∧
          ∀ i ∈ l, φ l E i = f^[PrizeAlloc.Interval.pos l i - 1] x := by sorry

end PrizeAlloc.SingleParam
