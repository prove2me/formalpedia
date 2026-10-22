-- Prove2me | Theorems.Thm_PrivSeqLearn_QueryComplexity_ob_accurate
-- name    : PrivSeqLearn.QueryComplexity.ob_accurate
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:15:21.759693+00:00
-- url     : https://prove2.me/theorems/9201b0f8-ca9d-42ae-b288-daba4a1c001a
-- title:
--   Proof of Proposition 6.2, Cases 1–2, p. 18 — the Opportunistic Bisection strategy is accurate
-- statement:
--   Let $\epsilon > 0$ and $L \ge 2$ be an integer with $2\epsilon < 1/L$. The Opportunistic Bisection strategy satisfies the accuracy constraint: for every true value $x \in [0,1)$ and every seed $y$,
--   $$|\hat x(x,y) - x| \le \frac{\epsilon}{2}.$$
--
--   In the paper's proof, either a guess $[i/L, i/L+\epsilon)$ of length $\epsilon$ contains $x$ and the estimate is its mid-point, or a truthful bisection of the sub-interval containing $x$ ends with an interval of length at most $\epsilon$ and the estimate is its mid-point. This is the accuracy half of Proposition 6.2.
--
--   **Formalization Note** The hypothesis $2\epsilon < 1/L$ is the regime $2\epsilon < \delta \le 1/L$ with $\delta$ eliminated, since $\delta$ does not enter accuracy.
-- source:
--   Tsitsiklis, Xu, Xu, Private Sequential Learning, arXiv:1805.02136v3, p. 18, proof of Proposition 6.2, Cases 1–2

import Mathlib
import Definitions.Def_PrivSeqLearn_QueryComplexity_Setting
import Definitions.Def_PrivSeqLearn_QueryComplexity_OB

namespace PrivSeqLearn.QueryComplexity

/-- The OB strategy is accurate (Tsitsiklis, Xu, Xu, Private Sequential Learning, arXiv:1805.02136v3, p. 18, proof of Proposition 6.2, Cases 1–2): for every
true value `x ∈ [0, 1)` and every seed, `|x̂(x, y) − x| ≤ ϵ/2`.

**Formalization Note** The hypothesis `2ϵ < 1/L` is the paper's regime `2ϵ < δ ≤ 1/L` with `δ`
eliminated (`δ` plays no role in accuracy). -/
theorem ob_accurate (ϵ : ℝ) (L : ℕ) (hϵ : 0 < ϵ) (hL : 2 ≤ L) (hϵL : 2 * ϵ < 1 / (L : ℝ)) :
    IsAccurate ϵ (obStrategy ϵ L (by omega)) := by sorry

end PrivSeqLearn.QueryComplexity
