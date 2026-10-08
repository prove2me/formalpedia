-- Prove2me | Theorems.Thm_SpikedWishart_Separated_lemma_1_1
-- name    : SpikedWishart.Separated.lemma_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:36:53.410037+00:00
-- url     : https://prove2.me/theorems/f4190bf7-9749-4d77-907d-2bef0aef5563
-- title:
--   Lemma 1.1, p. 1649 — G_k(x) = det(1 − H^(k)_x), the Hermite-kernel Fredholm determinant on L²((x,∞))
-- statement:
--   For every $k \ge 1$ and $x \in \mathbb R$,
--   $$
--   G_k(x) = \det\big(1 - \mathbf H^{(k)}_x\big),
--   $$
--   where $G_k$ is the distribution function (28) of the largest eigenvalue of the $k\times k$ GUE and $\mathbf H^{(k)}_x$ is the integral operator on $L^2((x,\infty))$ with kernel
--   $$
--   H^{(k)}(u,v) = \frac{c_{k-1}}{c_k}\,\frac{p_k(u)p_{k-1}(v) - p_{k-1}(u)p_k(v)}{u-v}\,e^{-(u^2+v^2)/4}
--   $$
--   of (34), $p_n$ the orthonormal polynomials (31) with leading coefficients $c_n$ (32).
--
--   This is the orthogonal-polynomial representation of the finite GUE, the form in which $G_k$ appears as the limit in the proof of Theorem 1.1(b).
--
--   **Formalization Note** The Fredholm determinant is the Fredholm series $\sum_n \frac{(-1)^n}{n!}\int_{(x,\infty)^n}\det[H^{(k)}(u_i,u_j)]\,du$, and $H^{(k)}$ takes its continuous value on the diagonal (see the GUE definition).
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), p. 1649, Lemma 1.1, (33)–(34)

import Mathlib
import Definitions.Def_SpikedWishart_Separated_GUE

namespace SpikedWishart.Separated

/-- Lemma 1.1, p. 1649: for `k ≥ 1` and real `x`, `G_k(x) = det(1 − H^{(k)}_x)`, the
Fredholm determinant on `L²((x, ∞))` of the kernel (34). -/
theorem lemma_1_1 (k : ℕ) (hk : 1 ≤ k) (x : ℝ) : G k x = SpikedWishart.SoftEdge.fredholmDet (Hk k) x := by sorry

end SpikedWishart.Separated
