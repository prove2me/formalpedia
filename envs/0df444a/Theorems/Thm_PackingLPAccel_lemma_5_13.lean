-- Prove2me | Theorems.Thm_PackingLPAccel_lemma_5_13
-- name    : PackingLPAccel.lemma_5_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:43:55.507525+00:00
-- url     : https://prove2.me/theorems/b5e69020-4a18-4aeb-9188-5c5caaa35d86
-- title:
--   Lemma 5.13 — the proxy $M$ sandwiches the Bregman divergence of $\|\cdot\|_q^{pq}$
-- statement:
--   Let $p\ge2$, $q=1+1/p$, $n\ge1$, $x\in\mathbb R^n_{\ge0}$, $y\in\mathbb R^n$ and $\omega=4096p^4$. Then
--
--   $$\omega M(y/\omega;x)\le V^{\|\cdot\|_q^{pq}}_x(x+y)\le M(y;x).$$
--
--   This is the new bound of the paper. It allows $p=\Theta(\log m)$ with $\omega=\widetilde O(1)$, which removes the $m^{o(1)}$ factors of the earlier framework.
--
--   Differences from the source:
--   - encoding: p, q, x as in Lemma 5.11 (not repeated) → p ≥ 2, q = 1 + 1/p, x ≥ 0; reason: the standing assumptions of the preceding lemma
--   - encoding: ∥x∥_q^{(p−2)q} at p = 2, x = 0 → Real.rpow gives 0^0 = 1; reason: the benign value; the inequality was tested with it at planning
-- source:
--   Chen, Chen, Graur, Sidford, Accelerated Parallel Algorithms for Packing Linear Programming, STOC 2027 submission (manuscript sha256 1dac7711…), Lemma 5.13, p.24 (pdf 25); proof pp.38–40 (pdf 39–41)

import Mathlib
import Definitions.Def_PackingLPAccel_Proxy

namespace PackingLPAccel

/-- **Lemma 5.13** (manuscript sha256 1dac7711…, p.24; proof pp.38–40). Standing assumptions as in Lemma 5.11;
`ω = 4096 p⁴` exactly. -/
theorem lemma_5_13 {n : ℕ} (_ : 0 < n) (p q : ℝ) (_ : 2 ≤ p) (_ : q = 1 + 1 / p)
    (x y : Fin n → ℝ) (_ : ∀ i, 0 ≤ x i) :
    4096 * p ^ 4 * proxyM p q (fun i => y i / (4096 * p ^ 4)) x ≤ bregPQ p q x y ∧
      bregPQ p q x y ≤ proxyM p q y x := by sorry

end PackingLPAccel
