-- Prove2me | Theorems.Thm_StochCoordProx_display_56_mgf_inequality
-- name    : StochCoordProx.display_56_mgf_inequality
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T11:32:47.38202+00:00
-- url     : https://prove2.me/theorems/5eb9b87e-65e4-4cd4-8b8e-a726431521c7
-- title:
--   (56) — $py+\log(1-p+pe^{-y})\le\frac{y^2p}{2}$
-- statement:
--   For all $p\in[0,1]$ and $y\ge0$,
--
--   $$
--   py+\log\bigl(1-p+pe^{-y}\bigr)\le\frac{y^2p}{2}.
--   $$
--
--   The argument of the logarithm is positive on this range. The inequality bounds the moment generating function of a centered Bernoulli variable, $\mathbb E[e^{-t(T-p)}]=e^{tp+\log(1-p+pe^{-t})}\le e^{t^2p/2}$, which is the step of the Chernoff argument in the proof of Lemma 6.
--
--   Differences from the source: none.
-- source:
--   Necoara & Chorobura, Efficiency of stochastic coordinate proximal gradient methods on nonseparable composite optimization, arXiv:2104.13370v3, proof of Lemma 6, display (56), p.26

import Mathlib

namespace StochCoordProx

/-- **Display (56)** (proof of Lemma 6): for all `p ∈ [0,1]` and `y ≥ 0`,
`p y + log(1 − p + p e^{−y}) ≤ y² p / 2`.

Necoara & Chorobura, arXiv:2104.13370v3, proof of Lemma 6, display (56), p.26.

**Formalization Note.** For `p ∈ [0,1]` and `y ≥ 0` the argument `1 − p + p e^{−y}` is positive,
so `Real.log` is the true logarithm here. -/
theorem display_56_mgf_inequality (p y : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hy : 0 ≤ y) :
    p * y + Real.log (1 - p + p * Real.exp (-y)) ≤ y ^ 2 * p / 2 := by sorry

end StochCoordProx
