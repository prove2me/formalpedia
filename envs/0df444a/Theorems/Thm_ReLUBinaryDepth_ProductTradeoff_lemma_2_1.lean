-- Prove2me | Theorems.Thm_ReLUBinaryDepth_ProductTradeoff_lemma_2_1
-- name    : ReLUBinaryDepth.ProductTradeoff.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:14:27.644798+00:00
-- url     : https://prove2.me/theorems/69b1dc75-11c0-4a07-bb23-ad08fbe93db5
-- title:
--   Lemma 2.1 — Boolean selector with a fixed dominating constant
-- statement:
--   Let $B>1$, let $\theta(0),\theta(1)\in[0,B]$, and fix one real constant $M$. For every $a\ge0$ such that $Ba\le M$, the selector satisfies both identities
--   $$S_{\theta,M}(0,a)=a\theta(0),\qquad S_{\theta,M}(1,a)=a\theta(1).$$
--   The same $M$ and the same two coefficients are fixed before quantifying over $a$. Thus these equalities hold on any bounded nonnegative domain on which $M$ dominates $Ba$. Zero coefficients, $a=0$, and equality $Ba=M$ are included.
--
--   The selector supplies an exact choice of one scaled coefficient from a Boolean input. It is the local operation required by the product recurrence.
--
--   Differences from the source:
--   - encoding: one fixed M dominates Ba on the allowed bounded nonnegative a-domain → M is fixed before all a>=0 with Ba<=M and both selector identities; reason: this is the pointwise form of the same bounded-domain assertion; no smaller a-domain or bit-dependent M is introduced
-- source:
--   Neil Krishnan, Elchanan Mossel, STOC 2027 submission #1645 (October 2026), Lemma 2.1, PDF p. 3 = printed p. 3. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1645.pdf

import Definitions.Def_ReLUBinaryDepth_ProductTradeoff_Product

namespace ReLUBinaryDepth.ProductTradeoff

/-- Lemma 2.1, PDF = printed p.3. The same M works for every admitted a and both bits. -/
theorem lemma_2_1 (B M : ℝ) (θ : Bool → ℝ) (hB : 1 < B)
    (hθ : ∀ b, 0 ≤ θ b ∧ θ b ≤ B) :
    ∀ a : ℝ, 0 ≤ a → B * a ≤ M →
      selector θ M false a = a * θ false ∧
      selector θ M true a = a * θ true := by sorry

end ReLUBinaryDepth.ProductTradeoff
