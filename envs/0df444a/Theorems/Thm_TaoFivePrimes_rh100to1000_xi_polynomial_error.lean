-- Prove2me | Theorems.Thm_TaoFivePrimes_rh100to1000_xi_polynomial_error
-- name    : TaoFivePrimes.rh100to1000_xi_polynomial_error
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-14T06:02:29.129987+00:00
-- url     : https://prove2.me/theorems/f1ae2511-d5da-4a49-84d3-ebdbe50c1ab9
-- title:
--   TaoFivePrimes.rh100to1000_xi_polynomial_error
-- statement:
--   For every center |T|<=1000, the entire xi function is uniformly enclosed within 10^(-356) on the closed unit disk by the finite 272-term local polynomial whose coefficients come from the exact Mellin quadrature formula. This completes the analytic polynomial approximation bound; rational evaluation and finite location certificates remain separate work.
-- source:
--   Extension of sometik179's xi/theta/Mellin and Cauchy-Taylor method, original c9908072-d99a-4431-aad8-a72c6352619a and accepted ordinary-syntax pilot 30db8e24-e604-49d7-ab5c-f7b6f516651a; theta/Mellin foundations attributed to Gabewhigham. Uses the accepted height-1000 local Taylor bound da08fb65-aa8c-4929-a7f7-2f69e3968a3d and the new full-range xi coefficient error. Ordinary Lean norm estimates combine the 272 coefficient errors with the exact Taylor remainder.

import Definitions.Def_TaoFivePrimes_RH100To1000XiPolynomial

theorem TaoFivePrimes.rh100to1000_xi_polynomial_error (T : ℝ) (hT : |T| ≤ 1000) (z : ℂ)
    (hz : ‖z-RH1000Analytic.CertifiedLocalXi.center T‖ ≤ 1) :
    ‖RH1000Analytic.CertifiedLocalXi.xi z-TaoFivePrimes_RH100To1000XiPolynomial T z‖ ≤ 1/10^356 := by sorry
