-- Prove2me | Theorems.Thm_R0J19Cert_b3_certs_lo
-- name    : R0J19Cert.b3_certs_lo
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T10:49:32.724932+00:00
-- url     : https://prove2.me/theorems/2803a689-a9de-4c47-8e12-e5de139078d3
-- title:
--   Peak-band lower-half integer quadrature certificates ($g=0,1,2$) for $r_{0,19}$
-- statement:
--   This theorem certifies the first three 8-column blocks ($g \in \{0,1,2\}$, covering $x_2$-grid bins $0$ through $23$ out of $48$) of the fused backward integer quadrature and convolution bound for the peak band $\varphi \in [2.10153, 2.12140]$ ($M_2 = 48$, $s = 6$, $M_1 = 288$) of the 4-dimensional Buchstab integral $I(\varphi)$ in `LL_Decomp587l.r0j19_short`.
--
--   Specifically, with denominator $D = 1{,}978{,}279{,}776$ and scaling $S = 10^9$, the checker `checkSJ8Go` verifies for each block $g \in \{0,1,2\}$ over all $812$ shifted $t$-rows and $525$ $u$-bins that the backward cumulative trapezoidal upper bounds match the stored boundary columns and that the weighted $H_m$-convolution sums satisfy
--
--   $$\sum_{r=8g}^{8g+7} \langle K_r, S_r \rangle \le J_{g,k} \cdot 10^6.$$
--
--   Together with `R0J19Cert.b3_certs_hi`, this establishes the certified upper bound on the peak band.
--
--   **Formalization Note** All quantities are pure `Nat` / `List Nat` computations imported from `Definitions.Def_r0j19_cert_core`.
-- source:
--   Wu (2004), Chen-type 4D Buchstab integral decomposition (supporting certificate lemma for LL_Decomp587l.r0j19_short, theorem_id deade48a-1e4e-40c1-8ddb-1d897d5e2e34)

import Definitions.Def_r0j19_cert_core
open R0J19Cert

namespace R0J19Cert

theorem b3_certs_lo :
  checkSJ8Go t0_b3 810770400 h_288 hy_48 err55_48 err110_48 6 240 525 false Ker_288_0 Ker_288_1 Ker_288_2 Ker_288_3 Ker_288_4 Ker_288_5 Ker_288_6 Ker_288_7 812 Bdry_b3_8 [] Jg_b3_0 [] [] [] [] [] [] [] [] = true ∧
  checkSJ8Go t0_b3 825511680 h_288 hy_48 err55_48 err110_48 6 192 525 true Ker_288_8 Ker_288_9 Ker_288_10 Ker_288_11 Ker_288_12 Ker_288_13 Ker_288_14 Ker_288_15 812 Bdry_b3_16 Bdry_b3_8 Jg_b3_1 [] [] [] [] [] [] [] [] = true ∧
  checkSJ8Go t0_b3 840252960 h_288 hy_48 err55_48 err110_48 6 144 525 true Ker_288_16 Ker_288_17 Ker_288_18 Ker_288_19 Ker_288_20 Ker_288_21 Ker_288_22 Ker_288_23 812 Bdry_b3_24 Bdry_b3_16 Jg_b3_2 [] [] [] [] [] [] [] [] = true := by sorry

end R0J19Cert
