-- Prove2me | Theorems.Thm_SpanForestStream_Unrestricted_eq_4_21
-- name    : SpanForestStream.Unrestricted.eq_4_21
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:31:51.773814+00:00
-- url     : https://prove2.me/theorems/7e19b40d-aa9f-43f6-a570-74d21d3fadc2
-- title:
--   Eq. (4.21) — state-entropy bound: H(M) ≤ E|M| + log(e(E|M| + 1)) = O(s + 1)
-- statement:
--   For a random binary string $M$ of expected length $L=\mathbb E|M|$ (with $L=\infty$ allowed),
--   $$H(M)\le L+\log_2\big(e\,(L+1)\big).$$
--   Consequently, for every fixed constant $a\ge 0$ there is a constant $C$ such that $\mathbb E|M|\le s+a$ implies $H(M)\le C(s+1)$ for every $s\ge 0$. In the source this is applied to the tagged prefix state $M_0$ of a streaming simulation, whose expected length is at most $s+O(1)$: its entropy is $O(s+1)$, which is how state length is charged in every information lower bound.
--
--   Differences from the source:
--   - generalization: the tagged original prefix state M0 of the simulation, with E|M0| ≤ s + O(1) → every law of a binary string M, and every additive constant a ≥ 0 in E|M| ≤ s + a; reason: the display applies the state-entropy bound of App. A.1 to M0; M0 is a random binary string and its O(1) is one fixed constant
--   - encoding: H(M0) = O(s + 1) → ∃ C > 0 (depending only on a) with H(M) ≤ C(s + 1) for all s ≥ 0; reason: O(·) as an explicit constant; the source's O(1) is absolute, so C is absolute
--   - encoding: entropy and expected length → [0,∞]-valued sums; at L = ∞ the bound reads H ≤ ∞; reason: no junk value for divergent sums
-- source:
--   Chao, Cen, Ma, Wang, Space-Optimal Algorithms for Spanning Forests in Dynamic Streams at Every Confidence Level, arXiv:2611.04365 (PDF sha256 00f5bb17…69c92), p. 32 (PDF 35), proof of Proposition 4.8, Eq. (4.21); p. 46 (PDF 49), proof of Lemma A.1

import Mathlib
import Definitions.Def_SpanForestStream_Unrestricted_Info

open scoped ENNReal

namespace SpanForestStream.Unrestricted

/-- Eq. (4.21), the state-entropy bound: a random binary string `M` of expected length
`L = E|M|` has `H(M) ≤ L + log₂(e (L + 1))`; consequently, if `E|M| ≤ s + a` for a fixed constant
`a`, then `H(M) = O(s + 1)`. -/
theorem eq_4_21 :
    (∀ μ : PMF (List Bool),
      entropyBits μ ≤ (∑' x, μ x * (x.length : ℝ≥0∞)) +
        ENNReal.ofReal
          (Real.logb 2 (Real.exp 1 * ((∑' x, μ x * (x.length : ℝ≥0∞)).toReal + 1)))) ∧
    ∀ a : ℝ, 0 ≤ a → ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 0 ≤ s → ∀ μ : PMF (List Bool),
      (∑' x, μ x * (x.length : ℝ≥0∞)) ≤ ENNReal.ofReal (s + a) →
        entropyBits μ ≤ ENNReal.ofReal (C * (s + 1)) := by sorry

end SpanForestStream.Unrestricted
