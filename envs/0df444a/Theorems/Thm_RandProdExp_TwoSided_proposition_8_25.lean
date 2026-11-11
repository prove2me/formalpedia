-- Prove2me | Theorems.Thm_RandProdExp_TwoSided_proposition_8_25
-- name    : RandProdExp.TwoSided.proposition_8_25
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:18:41.797356+00:00
-- url     : https://prove2.me/theorems/8744b388-18d6-4f00-9d2b-45a206916354
-- title:
--   Proposition 8.25 ([AZ06, Prop. 7.9]) — at most $2^NN^{3(N-2W+2)}$ equivalence classes of weak Wigner words
-- statement:
--   For all positive integers $N$ and $W$ with $N\ge2W-2$, there are at most
--   $$2^N\,N^{3(N-2W+2)}$$
--   equivalence classes of weak Wigner words of length $N+1$ and weight $W$. It is the counting input of the trace-moment bound in §8.
--
--   Differences from the source:
--   - reading: weak Wigner words over 'some alphabet' (Definition 8.10) → words over an arbitrary alphabet type α; reason: the alphabet is unspecified in the source; the bound is claimed for any
--   - encoding: N ≥ 2W − 2 and the exponent N − 2W + 2 → 2W ≤ N + 2 and the natural number N + 2 − 2W; reason: no truncated subtraction under the hypothesis
--   - encoding: 'there are at most X classes' → the set of classes is finite and its ncard is ≤ X; reason: ncard is 0 on infinite sets, so finiteness is stated explicitly; it is part of 'at most X'
-- source:
--   Chattopadhyay, Ringach, Spooner, Product Expansion of Random Codes via Analytic Techniques, STOC 2027 submission (manuscript sha256 9e4ac2d1…), p. 61, Proposition 8.25 (Proposition 7.9 of [AZ06])

import Mathlib
import Definitions.Def_RandProdExp_TwoSided_Words

namespace RandProdExp.TwoSided

/-- **Proposition 8.25** (Proposition 7.9 of [AZ06], p. 61). For all positive integers `N` and `W`
with `N ≥ 2W − 2`, there are at most `2^N N^{3(N − 2W + 2)}` equivalence classes of weak Wigner
words of length `N + 1` and weight `W` (over any alphabet). -/
theorem proposition_8_25 (α : Type) (N W : ℕ) (hN : 0 < N) (hW : 0 < W) (hNW : 2 * W ≤ N + 2) :
    (wignerClasses α N W).Finite ∧
      (wignerClasses α N W).ncard ≤ 2 ^ N * N ^ (3 * (N + 2 - 2 * W)) := by sorry

end RandProdExp.TwoSided
