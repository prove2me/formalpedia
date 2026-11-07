-- Prove2me | Theorems.Thm_PackingLPAccel_lemma_5_11
-- name    : PackingLPAccel.lemma_5_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:43:44.263669+00:00
-- url     : https://prove2.me/theorems/13bd6e2c-734b-4383-8e2c-99e6043b011b
-- title:
--   Lemma 5.11 — the positive movement against the Bregman divergence of $\|\cdot\|_q^q$
-- statement:
--   Let $p\ge2$, $q=1+1/p$ and $n\ge1$. For $x\in\mathbb R^n_{\ge0}$ and $y\in\mathbb R^n$, with $\mu(y;x)=\sum_i[(x_i+|y_i|)^q-x_i^q]$,
--
--   $$\mu(y;x)\le4\sqrt{\frac{\|x\|_q^qV^{\|\cdot\|_q^q}_x(x+y)}{q-1}}+\frac{2}{q-1}V^{\|\cdot\|_q^q}_x(x+y).$$
--
--   This lets the proxy $M$ use $\mu$ in place of the difference of $\|\cdot\|_q^q$ values.
--
--   Differences from the source:
--   - encoding: x ∈ ℝⁿ, ∑_{i∈[m]} → x ∈ ℝⁿ_{≥0}, ∑ over the n coordinates; reason: (x_i+|y_i|)^q needs x ≥ 0, as every X ∈ ℝ^{m×k}_{≥0}; [m] is a slip for [n]
-- source:
--   Chen, Chen, Graur, Sidford, Accelerated Parallel Algorithms for Packing Linear Programming, STOC 2027 submission (manuscript sha256 1dac7711…), Lemma 5.11, p.24 (pdf 25)

import Mathlib
import Definitions.Def_PackingLPAccel_Proxy

namespace PackingLPAccel

/-- **Lemma 5.11** (manuscript sha256 1dac7711…, p.24). `x ≥ 0`, since `(x_i + |y_i|)^q` needs it. -/
theorem lemma_5_11 {n : ℕ} (_ : 0 < n) (p q : ℝ) (_ : 2 ≤ p) (_ : q = 1 + 1 / p)
    (x y : Fin n → ℝ) (_ : ∀ i, 0 ≤ x i) :
    mu q y x ≤ 4 * Real.sqrt (qPow q x * bregQ q x y / (q - 1)) + 2 / (q - 1) * bregQ q x y := by sorry

end PackingLPAccel
