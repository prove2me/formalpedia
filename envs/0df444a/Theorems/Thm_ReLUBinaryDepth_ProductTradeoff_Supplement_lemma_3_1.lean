-- Prove2me | Theorems.Thm_ReLUBinaryDepth_ProductTradeoff_Supplement_lemma_3_1
-- name    : ReLUBinaryDepth.ProductTradeoff.Supplement.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:46:16.186655+00:00
-- url     : https://prove2.me/theorems/6ff64448-5aca-4cbb-bd81-69fd118f8147
-- title:
--   Lemma 3.1 — Depth-2 width-2 ReLU gadget for an integer threshold gate
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $m\ge 0$, let $a_1,\dots,a_m$ and $b$ be integers, and let $W$ be a natural number with
--   $$2+|b|+\sum_{j}|a_j|\le W.$$
--   Then the threshold gate $g(y)=\mathbf 1\bigl[\sum_j a_j y_j\ge b\bigr]$ on $y\in\{0,1\}^m$ is Boolean-computed (that is, $\mathbf 1[N(y)>\tfrac12]=g(y)$ for every $y$) by a strictly layered ReLU network $N$ with a ReLU output gate, of depth $2$ (one hidden layer plus the output layer) and width $2$, all of whose weights and biases are rationals with numerator and denominator of absolute value below $2^{C\lfloor\log_2 W\rfloor}$, i.e. $O(\log W)$-bit weights.
--
--   This gadget is the step of the proof of Theorem 3.2 that replaces each threshold gate by ReLU units.
--
--   Differences from the source:
--   - reading: a ReLU network (Section 3) → a network of the published class that is strictly layered (IsLayered) and has a ReLU output gate; reason: the proof of Theorem 3.2 uses layered gadgets; the narrower class makes this existence claim stronger, and it is still a network of the published class
--   - encoding: O(log W)-bit weights → ∃ C : ℕ, fixed before m, a, b, W, with HasBitWeights (C * Nat.log 2 W); reason: big-O with an absolute constant; W ≥ 2 so ⌊log₂ W⌋ ≥ 1 and log W ≤ 2⌊log₂ W⌋
--   - encoding: W (an unspecified bound) → W : ℕ; reason: the left side is an integer, so any real W can be replaced by ⌊W⌋ without changing the hypothesis or enlarging the bit bound
--   - encoding: depth 2, width 2 → N.depth = 2 (one hidden layer plus the counted output layer), N.width = 2; reason: the published depth and width count the output layer, matching the proof's two-layer gadget
-- source:
--   Neil Krishnan, Elchanan Mossel, Depth Lower Bounds for ReLU Networks with Binary Inputs, STOC 2027 submission #1645 (October 2026), Lemma 3.1, PDF p. 6 = printed p. 6; proof p. 7. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1645.pdf (SHA-256 35accc05b120367e3d7a527b3b55383bc4a42c205bc78904f41eea6b2668555b)

import Definitions.Def_ReLUBinaryDepth_ProductTradeoff_Supplement_Layered

namespace ReLUBinaryDepth.ProductTradeoff.Supplement

open ReLUBinaryDepth.ProductTradeoff

/-- Lemma 3.1, PDF = printed p. 6. The constant `C` of `O(log W)` is fixed before `m, a, b, W`. -/
theorem lemma_3_1 :
    ∃ C : ℕ, ∀ (m : ℕ) (a : Fin m → ℤ) (b : ℤ) (W : ℕ),
      2 + |b| + ∑ j, |a j| ≤ (W : ℤ) →
      ∃ N : Network m, IsLayered N ∧ N.outputRelu = true ∧ N.depth = 2 ∧ N.width = 2 ∧
        HasBitWeights (C * Nat.log 2 W) N ∧
        BoolComputes N (fun y => decide (b ≤ ∑ j, a j * (if y j then 1 else 0))) := by sorry

end ReLUBinaryDepth.ProductTradeoff.Supplement
