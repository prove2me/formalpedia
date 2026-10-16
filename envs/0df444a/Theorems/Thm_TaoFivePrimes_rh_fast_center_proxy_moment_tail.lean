-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_center_proxy_moment_tail
-- name    : TaoFivePrimes.rh_fast_center_proxy_moment_tail
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T09:31:10.628018+00:00
-- url     : https://prove2.me/theorems/8c02447d-fb92-4bec-8887-6b5c0d4abe1a
-- title:
--   TaoFivePrimes.rh_fast_center_proxy_moment_tail
-- statement:
--   For every natural center3000000256<=T<=3300000000, every natural normalized-moment order and |t|>=256, the actual center-polynomial proxy moment has norm at most35exp(-|t|/4). No Fourier evaluation or complete RH window is asserted.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198; Gaussian/Hermite Fourier identities and center Stirling expansion. Original surrounding attribution retained: sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastGaussianWindowFourier

theorem TaoFivePrimes.rh_fast_center_proxy_moment_tail (T:Nat) (hT:3000000256≤T) (hU:T≤3300000000) (k:Nat) (t:ℝ)
 (ht:256≤|t|) : ‖RHFastGaussianWindow.momentProxy T k t‖≤35*Real.exp (-|t|/4) := by sorry
