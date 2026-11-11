-- Prove2me | Theorems.Thm_ReLUBinaryDepth_ProductTradeoff_lemma_2_3
-- name    : ReLUBinaryDepth.ProductTradeoff.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:13:44.375592+00:00
-- url     : https://prove2.me/theorems/ff76bd78-c4b4-42e4-8fd5-e651e3523bef
-- title:
--   Lemma 2.3 — Uniform bound on the rational output span
-- statement:
--   There is an absolute real constant $C>0$ such that, for every $n,w\ge0$, every network $N$ with $n\le w$ and computed width at most $w$, and every $f:\{0,1\}^n\to\mathbb R$ computed exactly by $N$,
--   $$\dim_{\mathbb Q}\operatorname{span}_{\mathbb Q}\{f(x):x\in\{0,1\}^n\}\le Cw^{\operatorname{depth}(N)}.$$
--   The constant precedes all network parameters; weights and biases are arbitrary real numbers. The network always contains its output, so its depth and computed width are positive. The case $w=1$ is included. Finite dimensionality follows from the finite Boolean domain, independently of the displayed bound.
--
--   This is an arithmetic restriction on exact output values. It provides the dimension estimate used for the exponential product lower bound.
--
--   Differences from the source:
--   - reading: network syntax and input-terminal counting are unspecified → raw Boolean inputs are available at every layer and are excluded from computational width; reason: Lemma 2.2 reads a fresh input at each stage while claiming constant width and counts the final summation gate
--   - generalization: ReLU network with the construction using adjacent computed layers → competitors may use every earlier computed layer and an affine final-output mode; reason: ordinary layered ReLU networks embed by setting extra weights to zero and selecting ReLU output; the uniform output-span bound also holds for the broader class
--   - generalization: a function on n Boolean coordinates → n may also be zero, with a singleton input cube and an arbitrary network output; reason: this adds the empty-input case, whose output span has dimension at most one, and preserves every positive-dimensional instance
--   - encoding: depth d and width w → depth is the number of hidden layers plus one and w is any upper bound on the computed maximum layer width; reason: the final output gate counts as one layer and one unit; raw inputs do not count
--   - encoding: rational dimension of the span of the finite output range → Module.finrank over rational scalars with finite dimensionality supplied by a finite-generation instance; reason: the cube is finite, so finrank is the actual dimension rather than a nonfinite default
--   - encoding: O(w^d) → one positive real constant before every input size, network and resource parameter; reason: this makes the source asymptotic constants absolute without changing the rate
-- source:
--   Neil Krishnan, Elchanan Mossel, STOC 2027 submission #1645 (October 2026), Lemma 2.3, PDF p. 4 = printed p. 4; proof continues on p. 5. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1645.pdf

import Definitions.Def_ReLUBinaryDepth_ProductTradeoff_Network

namespace ReLUBinaryDepth.ProductTradeoff

/-- Lemma 2.3, PDF = printed pp.4–5. A single absolute constant, including w=1.
The outputSpanFinite instance supplies finite dimensionality before finrank is used. -/
theorem lemma_2_3 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n w : ℕ) (N : Network n) (f : Cube n → ℝ),
      n ≤ w → N.width ≤ w → N.Computes f →
      (Module.finrank ℚ (outputSpan f) : ℝ) ≤ C * (w : ℝ) ^ N.depth := by sorry

end ReLUBinaryDepth.ProductTradeoff
