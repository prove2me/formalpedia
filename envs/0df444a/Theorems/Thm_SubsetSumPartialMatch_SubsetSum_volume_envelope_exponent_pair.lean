-- Prove2me | Theorems.Thm_SubsetSumPartialMatch_SubsetSum_volume_envelope_exponent_pair
-- name    : SubsetSumPartialMatch.SubsetSum.volume_envelope_exponent_pair
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:24.743458+00:00
-- url     : https://prove2.me/theorems/2b6b4f14-6552-4983-bbe0-3316b0491265
-- title:
--   Corollary 3.9 — the constructed volume envelope
-- statement:
--   Let $a,b$ and $V_L,V_R$ be as in Theorem 3.8 and define
--   $$V(t)=\max_{a\le\mu\le2a,\ \mu\le\theta\le2\mu}\bigl\{t\,V_L(\mu,\theta)+(1-t)\,V_R(\mu,\theta)\bigr\}\quad(t\in[0,1]).$$
--   Then $V$ is nonnegative on $[0,1]$, and every pair $(l,r)\in\mathbb R^2$ with
--   $$t\,l+(1-t)\,r\ge\min\Bigl\{V(t),\,t,\,\frac{1-t}2\Bigr\}\quad\text{for all }t\in[0,1]$$
--   belongs to $K(1/2)$.
--
--   This is the circuit-side input to the main theorem.
--
--   Differences from the source:
--   - encoding: $\max$ over the compact domain → `sSup` of the image of the domain; reason: the domain is compact and nonempty for $a>0$ and the objective is continuous, so the supremum is the maximum
-- source:
--   Li & Ye, Subset Sum via Partial Match, STOC 2027 submission #24, preprint, source.pdf sha256 e5f396c346fb73c14219a019a35c9a16b1adc4b4b84978d3658736d31958ae5c, p. 27, Corollary 3.9

import Mathlib
import Definitions.Def_SubsetSumPartialMatch_SubsetSum_Circuit
import Definitions.Def_SubsetSumPartialMatch_SubsetSum_Entropy

namespace SubsetSumPartialMatch.SubsetSum

/-- Corollary 3.9. With `a, b` as in Theorem 3.8 and
`V(t) = max_{a≤µ≤2a, µ≤θ≤2µ} (t V_L(µ,θ) + (1-t) V_R(µ,θ))`, the function `V` is nonnegative on
`[0,1]`, and every `(l, r) ∈ ℝ²` with `t l + (1-t) r ≥ min {V(t), t, (1-t)/2}` for all `t ∈ [0,1]`
belongs to `K(1/2)`. -/
theorem volume_envelope_exponent_pair {a b : ℝ} (ha : 0 < a) (hab : 4 * a ≤ 1 - b)
    (hb : 1 - b ≤ 1 / 2) (hκ : 4 * a < kappa a b) :
    (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ volumeEnvelope a b t) ∧
    ∀ l r : ℝ,
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        min (volumeEnvelope a b t) (min t ((1 - t) / 2)) ≤ t * l + (1 - t) * r) →
      (l, r) ∈ K (1 / 2) := by sorry

end SubsetSumPartialMatch.SubsetSum
