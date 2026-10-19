-- Prove2me | Theorems.Thm_PrivSeqLearn_QueryComplexity_coverNumber_mono
-- name    : PrivSeqLearn.QueryComplexity.coverNumber_mono
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:14:19.685905+00:00
-- url     : https://prove2.me/theorems/332bb8db-0bfd-431b-aadd-1c6ac4718007
-- title:
--   Proof of Proposition 6.2, p. 18 — if U ⊂ V and C_δ(U) ≥ L then C_δ(V) ≥ L
-- statement:
--   Let $\delta > 0$, $L \in \mathbb N$, and let $U \subseteq V \subseteq \mathbb R$ with $V$ bounded. If $C_\delta(U) \ge L$, then
--   $$C_\delta(V) \ge L.$$
--
--   A cover of $V$ is a cover of $U$, so the cover number is monotone under inclusion; the paper uses this to pass from $C_\delta(\mathcal G) \ge L$ to $C_\delta(\mathcal I(\bar q)) \ge L$.
--
--   **Formalization Note** Boundedness of $V$ and $\delta > 0$ ensure that $V$ is $(\delta, L')$-coverable for some $L'$, so $C_\delta(V)$ is a genuine minimum; without it the Lean value of the minimum of an empty set of naturals is $0$. In the paper $V$ is an information set, a subset of $[0,1)$.
-- source:
--   Tsitsiklis, Xu, Xu, Private Sequential Learning, arXiv:1805.02136v3, p. 18, proof of Proposition 6.2 (monotonicity of the cover number)

import Mathlib
import Definitions.Def_PrivSeqLearn_QueryComplexity_Setting

namespace PrivSeqLearn.QueryComplexity

/-- Monotonicity of the cover number (Tsitsiklis, Xu, Xu, Private Sequential Learning, arXiv:1805.02136v3, p. 18): for `U ⊆ V`, if `C_δ(U) ≥ L` then
`C_δ(V) ≥ L`.

**Formalization Note** `V` is assumed bounded and `δ > 0`, so that `V` is `(δ, L')`-coverable for some
`L'` and `coverNumber δ V` is a true minimum; for an uncoverable `V` the Lean value is `sInf ∅ = 0`.
In the paper the lemma is applied to `V = I(q) ⊆ [0, 1)`. -/
theorem coverNumber_mono (δ : ℝ) (L : ℕ) (U V : Set ℝ) (hδ : 0 < δ) (hUV : U ⊆ V)
    (hV : Bornology.IsBounded V) (hU : L ≤ coverNumber δ U) :
    L ≤ coverNumber δ V := by sorry

end PrivSeqLearn.QueryComplexity
