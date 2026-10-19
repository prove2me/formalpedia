-- Prove2me | Theorems.Thm_PrivSeqLearn_QueryComplexity_claim_6_3
-- name    : PrivSeqLearn.QueryComplexity.claim_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:15:19.710432+00:00
-- url     : https://prove2.me/theorems/8bad1d77-1373-4be4-9f52-dee1089e3697
-- title:
--   Claim 6.3, p. 18 — the δ-cover number of the union of guesses G is at least L
-- statement:
--   Let $\epsilon > 0$, $\delta > 0$ and $L \ge 2$ an integer with $2\epsilon < \delta \le 1/L$, and let $\mathcal G = \bigcup_{i=0}^{L-1} [i/L, i/L + \epsilon)$ be the union of the $L$ guesses of the Opportunistic Bisection strategy (eq. (19)). Then
--   $$C_\delta(\mathcal G) \ge L,$$
--   that is, $\mathcal G$ cannot be covered by fewer than $L$ closed intervals of length at most $\delta$.
--
--   Together with Claim 6.4 and the monotonicity of the cover number, this gives the privacy half of Proposition 6.2.
-- source:
--   Tsitsiklis, Xu, Xu, Private Sequential Learning, arXiv:1805.02136v3, p. 18, Claim 6.3 (with eq. (19))

import Mathlib
import Definitions.Def_PrivSeqLearn_QueryComplexity_Setting
import Definitions.Def_PrivSeqLearn_QueryComplexity_OB

namespace PrivSeqLearn.QueryComplexity

/-- Claim 6.3 (Tsitsiklis, Xu, Xu, Private Sequential Learning, arXiv:1805.02136v3, p. 18): the `δ`-cover number of the union of guesses
`G = ⋃_{i<L} [i/L, i/L + ϵ)` (eq. (19)) is at least `L`, in the regime of Proposition 6.2. -/
theorem claim_6_3 (ϵ δ : ℝ) (L : ℕ) (hϵ : 0 < ϵ) (hδ : 0 < δ) (hL : 2 ≤ L)
    (h2ϵδ : 2 * ϵ < δ) (hδL : δ ≤ 1 / (L : ℝ)) :
    L ≤ coverNumber δ (guessUnion ϵ L) := by sorry

end PrivSeqLearn.QueryComplexity
