-- Prove2me | Theorems.Thm_TaoFivePrimes_rh124p5_xi_polynomial_derivative_bound
-- name    : TaoFivePrimes.rh124p5_xi_polynomial_derivative_bound
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:56:18.029299+00:00
-- url     : https://prove2.me/theorems/fe51039f-0b39-4c90-ae7b-43c9ae5641b6
-- title:
--   Derivative bound for the height-124.5 xi approximation
-- statement:
--   Let $c=1/2+124.5i$, let $\xi$ be the completed Riemann xi function, and let $P$ be the stored rounded local polynomial padded with zeros through degree 59. Put $F(z)=10^{40}\xi(z)-P(z)$. For $|z-c|\le63/20$,
--
--   $$
--   |F'(z)|\le2.
--   $$
--
--   This derivative estimate supports critical-line zero-location arguments near height $127.5$.
-- source:
--   Derived from the proved 320-moment enclosure and exact rational translation. The xi/Taylor and Bernstein frameworks are due to sometik179, with theta/Mellin foundations by Gabewhigham. Related finite-height verification: Tao, arXiv:1201.6656v4, Theorem 1.5, https://arxiv.org/abs/1201.6656; Platt, https://doi.org/10.1090/mcom/3198.

import Definitions.Def_TaoFivePrimes_RHLocalRationalPolynomial
import Definitions.Def_TaoFivePrimes_RH124p5RoundedCoefficients14
import Mathlib.Tactic

theorem TaoFivePrimes.rh124p5_xi_polynomial_derivative_bound (z : ℂ)
    (hz : ‖z-RH1000Analytic.CertifiedLocalXi.center (249/2)‖ ≤ (63/20:ℝ)) :
    ‖deriv (fun w : ℂ => ((10^40:ℕ):ℂ)*RH1000Analytic.CertifiedLocalXi.xi w-
      TaoFivePrimes_RHLocalRationalPolynomial TaoFivePrimes_RH124p5RoundedCoefficients14
        (10^14) 60 (249/2) w) z‖ ≤ 2 := by sorry
