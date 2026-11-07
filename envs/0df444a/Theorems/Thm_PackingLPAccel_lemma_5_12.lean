-- Prove2me | Theorems.Thm_PackingLPAccel_lemma_5_12
-- name    : PackingLPAccel.lemma_5_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:43:56.961453+00:00
-- url     : https://prove2.me/theorems/c2833d0f-7810-4084-aa82-b60f8277c1e1
-- title:
--   Lemma 5.12 — the Bregman divergence of $|\cdot|^p$, cited from [AKPS22]
-- statement:
--   For every $p\ge2$ and $x,y\in\mathbb R$,
--
--   $$V^{|\cdot|^p}_x(x+y)\le2p^2|x|^{p-2}y^2+p^p|y|^p.$$
--
--   The proxy $M$ uses this bound on the outer function in the chain rule (15).
--
--   Differences from the source: none.
-- source:
--   Chen, Chen, Graur, Sidford, Accelerated Parallel Algorithms for Packing Linear Programming, STOC 2027 submission (manuscript sha256 1dac7711…), Lemma 5.12, p.24 (pdf 25), cited there as Lemma 2.5 in [AKPS22]

import Mathlib
import Definitions.Def_PackingLPAccel_Proxy

namespace PackingLPAccel

/-- **Lemma 5.12** (manuscript sha256 1dac7711…, p.24), cited there as Lemma 2.5 in [AKPS22]. `x` is signed;
the derivative of `|·|^p` at `x` is `p |x|^{p-1} sign x`. -/
theorem lemma_5_12 (p x y : ℝ) (_ : 2 ≤ p) :
    bregAbs p x y ≤ 2 * p ^ 2 * |x| ^ (p - 2) * y ^ 2 + p ^ p * |y| ^ p := by sorry

end PackingLPAccel
