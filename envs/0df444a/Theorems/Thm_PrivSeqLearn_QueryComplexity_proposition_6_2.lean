-- Prove2me | Theorems.Thm_PrivSeqLearn_QueryComplexity_proposition_6_2
-- name    : PrivSeqLearn.QueryComplexity.proposition_6_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:15:20.675987+00:00
-- url     : https://prove2.me/theorems/8bfa678f-c4c7-4e85-a6dd-75ef641daefb
-- title:
--   Proposition 6.2, p. 18 — for 2ϵ < δ ≤ 1/L the Opportunistic Bisection strategy is (ϵ,δ,L)-private
-- statement:
--   Fix $\epsilon > 0$, $\delta > 0$ and an integer $L \ge 2$ such that $2\epsilon < \delta \le 1/L$. Then the Opportunistic Bisection strategy $\phi^{\mathrm{OB}}$, of length $2L + \lceil \log_2(1/(\epsilon L)) \rceil$, is
--   $$(\epsilon, \delta, L)\text{-private}:$$
--   it is accurate, and $C_\delta(\mathcal I(\bar q)) \ge L$ for every $x \in [0,1)$ and every $\bar q \in \mathcal Q(x)$.
--
--   With the membership of $\phi^{\mathrm{OB}}$ in $\Phi_N$, this gives the upper bound $N^*(\epsilon,\delta,L) \le \lceil \log_2(1/(L\epsilon)) \rceil + 2L$ of Theorem 4.1.
-- source:
--   Tsitsiklis, Xu, Xu, Private Sequential Learning, arXiv:1805.02136v3, p. 18, Proposition 6.2

import Mathlib
import Definitions.Def_PrivSeqLearn_QueryComplexity_Setting
import Definitions.Def_PrivSeqLearn_QueryComplexity_OB

namespace PrivSeqLearn.QueryComplexity

/-- Proposition 6.2 (Tsitsiklis, Xu, Xu, Private Sequential Learning, arXiv:1805.02136v3, p. 18): fix `ϵ > 0`, `δ > 0` and an integer `L ≥ 2` with
`2ϵ < δ ≤ 1/L`. Then the Opportunistic Bisection strategy is `(ϵ, δ, L)`-private. -/
theorem proposition_6_2 (ϵ δ : ℝ) (L : ℕ) (hϵ : 0 < ϵ) (hδ : 0 < δ) (hL : 2 ≤ L)
    (h2ϵδ : 2 * ϵ < δ) (hδL : δ ≤ 1 / (L : ℝ)) :
    IsPrivate ϵ δ L (obStrategy ϵ L (by omega)) := by sorry

end PrivSeqLearn.QueryComplexity
