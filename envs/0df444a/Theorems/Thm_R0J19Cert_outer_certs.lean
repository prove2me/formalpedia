-- Prove2me | Theorems.Thm_R0J19Cert_outer_certs
-- name    : R0J19Cert.outer_certs
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T10:49:33.75009+00:00
-- url     : https://prove2.me/theorems/be5d10be-2a77-4f04-aa59-cf794d07af8e
-- title:
--   Outer-band integer quadrature certificates ($b_1, b_2, b_4, b_5$) for $r_{0,19}$
-- statement:
--   This theorem certifies all integer quadrature, kernel-weight, sliding-window, and slice-convolution inequalities for the four non-peak bands $b_1, b_2, b_4, b_5$ covering $[2, 2.10153] \cup [2.12140, 2.28813]$ (using coarse tiers $(M_2, s) = (8, 2)$ and $(16, 3)$) of the 4-dimensional Buchstab integral $I(\varphi)$ in `LL_Decomp587l.r0j19_short`.
--
--   For every certified slice across all four bands, the discrete convolution bound verifies
--
--   $$\sum_{d} W_{0,d}\, J_{\mathrm{win}, p\cdot m + d} \le 70{,}737 \cdot 10^9,$$
--
--   yielding $I(\varphi) \le 70{,}737 \times 10^{-9}$ away from the peak band.
--
--   **Formalization Note** All quantities are pure `Nat` / `List Nat` computations imported from `Definitions.Def_r0j19_cert_core`.
-- source:
--   Wu (2004), Chen-type 4D Buchstab integral decomposition (supporting certificate lemma for LL_Decomp587l.r0j19_short, theorem_id deade48a-1e4e-40c1-8ddb-1d897d5e2e34)

import Definitions.Def_r0j19_cert_core
open R0J19Cert

namespace R0J19Cert

theorem outer_certs :
  checkW0Go h_16 23 A1_num W0_cert_16 = true ∧
  checkKersAll 2 hy_8 h_16 0 Kers_16 = true ∧
  checkW0Go h_48 67 A1_num W0_cert_48 = true ∧
  checkKersAll 3 hy_16 h_48 0 Kers_48 = true ∧
  checkSJ8Go t0_b1 810770400 h_16 hy_8 err55_8 err110_8 2 0 55 false Ker_16_0 Ker_16_1 Ker_16_2 Ker_16_3 Ker_16_4 Ker_16_5 Ker_16_6 Ker_16_7 70 [] [] Jg_b1_0 [] [] [] [] [] [] [] [] = true ∧
  checkJ1Sum Jg_b1_0 Jc_b1.reverse = true ∧
  checkJWin4 Jc_b1 Jw_b1 = true ∧
  checkSlices 8 4 W0_cert_16 Jw_b1 = true ∧
  checkSJ8Go t0_b2 810770400 h_48 hy_16 err55_16 err110_16 3 24 80 false Ker_48_0 Ker_48_1 Ker_48_2 Ker_48_3 Ker_48_4 Ker_48_5 Ker_48_6 Ker_48_7 127 Bdry_b2_8 [] Jg_b2_0 [] [] [] [] [] [] [] [] = true ∧
  checkSJ8Go t0_b2 854994240 h_48 hy_16 err55_16 err110_16 3 0 80 true Ker_48_8 Ker_48_9 Ker_48_10 Ker_48_11 Ker_48_12 Ker_48_13 Ker_48_14 Ker_48_15 127 [] Bdry_b2_8 Jg_b2_1 [] [] [] [] [] [] [] [] = true ∧
  checkJ2Sum Jg_b2_0 Jg_b2_1 Jc_b2.reverse = true ∧
  checkJWin1 Jc_b2 Jw_b2 = true ∧
  checkSlices 13 1 W0_cert_48 Jw_b2 = true ∧
  checkSJ8Go t0_b4 810770400 h_48 hy_16 err55_16 err110_16 3 24 90 false Ker_48_0 Ker_48_1 Ker_48_2 Ker_48_3 Ker_48_4 Ker_48_5 Ker_48_6 Ker_48_7 137 Bdry_b4_8 [] Jg_b4_0 [] [] [] [] [] [] [] [] = true ∧
  checkSJ8Go t0_b4 854994240 h_48 hy_16 err55_16 err110_16 3 0 90 true Ker_48_8 Ker_48_9 Ker_48_10 Ker_48_11 Ker_48_12 Ker_48_13 Ker_48_14 Ker_48_15 137 [] Bdry_b4_8 Jg_b4_1 [] [] [] [] [] [] [] [] = true ∧
  checkJ2Sum Jg_b4_0 Jg_b4_1 Jc_b4.reverse = true ∧
  checkJWin1 Jc_b4 Jw_b4 = true ∧
  checkSlices 23 1 W0_cert_48 Jw_b4 = true ∧
  checkSJ8Go t0_b5 810770400 h_16 hy_8 err55_8 err110_8 2 0 75 false Ker_16_0 Ker_16_1 Ker_16_2 Ker_16_3 Ker_16_4 Ker_16_5 Ker_16_6 Ker_16_7 90 [] [] Jg_b5_0 [] [] [] [] [] [] [] [] = true ∧
  checkJ1Sum Jg_b5_0 Jc_b5.reverse = true ∧
  checkJWin4 Jc_b5 Jw_b5 = true ∧
  checkSlices 13 4 W0_cert_16 Jw_b5 = true := by sorry

end R0J19Cert
