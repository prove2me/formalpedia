-- Prove2me | Theorems.Thm_TaoFivePrimes_theorem51_typeI_bound
-- name    : TaoFivePrimes.theorem51_typeI_bound
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-12T17:07:39.803059+00:00
-- url     : https://prove2.me/theorems/d0fdae67-dec9-4bf7-9f8e-7772e9446b85
-- title:
--   Unit-numerator Type I bound with explicit constant 96/pi²
-- statement:
--   Let U,V≥40, UV≤x/4, UV<q−1, a∈ℤ with |a|=1, and 4α=a/q+β with |β|≤q⁻². For every coefficient family with |c_d|≤1 on the positive odd d≤UV,
--
--   $$T_I(x,\alpha,U,V;c)\le\frac{96}{\pi^2}\frac{x}{(x/q)^2}\log(4x)\log\!\left(\frac{4eq}{\pi}\right).$$
--
--   The hypotheses imply x≥6400 and q≥1602. This is the actual Type I sum, without an assumed variation, smoothness, or Fourier-decay estimate.
-- source:
--   Tao, arXiv:1201.6656v4, Section 5.2, equation (5.18), for the Type I sum defined before (5.8). The proof uses discrete second differences and a corrected unit-phase sine estimate rather than the source intermediate comparison. https://arxiv.org/html/1201.6656v4#S5.SS2

import Definitions.Def_TaoFivePrimes_Theorem51Sums
open TaoFivePrimes

theorem TaoFivePrimes.theorem51_typeI_bound
    (x alpha beta U V : ℝ) (a : ℤ) (q : ℕ) (c : ℕ → ℂ)
    (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUVx : U * V ≤ x / 4) (hUVq : U * V < (q : ℝ) - 1)
    (ha : a.natAbs = 1)
    (hc : ∀ d ∈ theorem51Divisors U V, ‖c d‖ ≤ 1)
    (hphase : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) :
    theorem51TypeI x alpha U V c ≤
      (96 / Real.pi ^ 2) * (x / (x / q) ^ 2) *
        Real.log (4 * x) * Real.log (4 * Real.exp 1 * q / Real.pi) := by sorry
