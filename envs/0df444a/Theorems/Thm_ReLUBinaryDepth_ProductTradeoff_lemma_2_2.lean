-- Prove2me | Theorems.Thm_ReLUBinaryDepth_ProductTradeoff_lemma_2_2
-- name    : ReLUBinaryDepth.ProductTradeoff.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:15:29.327076+00:00
-- url     : https://prove2.me/theorems/4f4127c0-aa7c-4d70-b6b5-693d35699d56
-- title:
--   Lemma 2.2 — The constructed constant-width product network
-- statement:
--   Let $n\ge0$, $B>1$ and $0\le\theta_i(b)\le B$. Set $M=B^n$ and $a(0)=1$, and use the selector recurrence from the product definitions. The circuit constructed from these constants satisfies
--   $$\operatorname{depth}(N)=n+1,\qquad \operatorname{width}(N)\le2,\qquad N(x)=a(n)=\prod_i\theta_i(x_i)\quad\text{for every }x\in\{0,1\}^n.$$
--   Its output mode is ReLU. This statement attests both the numerical recurrence and evaluation of the actual gates. In particular, its final summation is a counted layer, rather than an uncounted arithmetic operation.
--
--   This is the unconditional realization result. No rational independence is required, and all zero coefficients remain allowed.
--
--   Differences from the source:
--   - reading: network syntax and input-terminal counting are unspecified → raw Boolean inputs are available at every layer and are excluded from computational width; reason: Lemma 2.2 reads a fresh input at each stage while claiming constant width and counts the final summation gate
--   - generalization: n coordinates indexed from 1 to n → n may also be zero, with empty product 1 and a single final output ReLU; reason: this adds an empty-input case and preserves every positive-dimensional instance
--   - encoding: coordinates i=1,...,n and accumulator a_1=1 → coordinates are Fin n and accumulator a(0)=1 with constant extension after stage n; reason: zero-based reindexing changes no product or stage up to n
--   - encoding: constant width, with two ReLU units per product layer and one final sum unit → the constructed circuit has width at most 2 and ReLU output; reason: this makes the source construction resource count explicit without adding an assumption
-- source:
--   Neil Krishnan, Elchanan Mossel, STOC 2027 submission #1645 (October 2026), Lemma 2.2, PDF p. 4 = printed p. 4. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1645.pdf

import Definitions.Def_ReLUBinaryDepth_ProductTradeoff_Construction

namespace ReLUBinaryDepth.ProductTradeoff

/-- Lemma 2.2, PDF = printed p.4. Includes the constructed circuit, not just a sequence identity.
The empty cube uses the one final output gate with bias 1. -/
theorem lemma_2_2 (n : ℕ) (B : ℝ) (θ : Fin n → Bool → ℝ) (hθ : Admissible B θ) :
    (productNetwork B θ).depth = n + 1 ∧
    (productNetwork B θ).width ≤ 2 ∧
    (productNetwork B θ).outputRelu = true ∧
    (productNetwork B θ).Computes (productMap θ) ∧
    ∀ x : Cube n,
      accumulator B θ x n = productMap θ x ∧
      (productNetwork B θ).eval x = accumulator B θ x n := by sorry

end ReLUBinaryDepth.ProductTradeoff
