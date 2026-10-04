-- Prove2me | Theorems.Thm_TaoFivePrimes_theorem51_vaughan_split
-- name    : TaoFivePrimes.theorem51_vaughan_split
-- status  : Open
-- author  : @Yuxuan Xu
-- created : 2026-09-12T17:07:38.438139+00:00
-- url     : https://prove2.me/theorems/197dea21-9471-497e-ba7a-3372b3e6eab7
-- title:
--   Centered Vaughan decomposition for the smoothed odd sum
-- statement:
--   Let U,V≥40, U,V<x, UV≤x/4 and x≤UV². There are complex coefficients c_d with |c_d|≤1 for every positive odd d≤UV such that
--
--   $$|S_{\eta_0,2}(x,\alpha)|\le T_I(x,\alpha,U,V;c)+T_{II}(x,\alpha,U,V).$$
--
--   The two sums are the literal sums of the imported interface. This is the algebraic decomposition obligation, independent of rational approximation to α. It asserts no analytic bound for either sum.
-- source:
--   Tao, arXiv:1201.6656v4, Lemma 4.11 and its application in Section 5 preceding (5.8). eta0 vanishes at the support endpoints, so UV≤x/4 and x≤UV² give the required open support. https://arxiv.org/html/1201.6656v4#S5

import Definitions.Def_TaoFivePrimes_Theorem51Sums

theorem TaoFivePrimes.theorem51_vaughan_split
    (x alpha U V : ℝ) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUx : U < x) (hVx : V < x)
    (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    ∃ c : ℕ → ℂ,
      (∀ d ∈ TaoFivePrimes.theorem51Divisors U V, ‖c d‖ ≤ 1) ∧
      ‖TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 2 x alpha‖ ≤
        TaoFivePrimes.theorem51TypeI x alpha U V c +
          TaoFivePrimes.theorem51TypeII x alpha U V := by sorry
