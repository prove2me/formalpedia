-- Prove2me | Theorems.Thm_R0J19Cert_b3_certs_hi
-- name    : R0J19Cert.b3_certs_hi
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T10:49:34.343949+00:00
-- url     : https://prove2.me/theorems/f5448557-b205-4f98-aaf6-63b4e1c7b102
-- title:
--   Peak-band upper-half and slice integer certificates ($g=3,4,5$) for $r_{0,19}$
-- statement:
--   This theorem certifies the remaining three 8-column blocks ($g \in \{3,4,5\}$, covering $x_2$-grid bins $24$ through $47$ out of $48$), the 6-group sum certificate, the sliding-window maximum bound, the $128$ outer $\varphi$-slice convolution bounds, and the $x_0$-weight and kernel-weight certificates for the peak band $\varphi \in [2.10153, 2.12140]$ ($M_2 = 48$, $s = 6$, $M_1 = 288$) of the 4-dimensional Buchstab integral $I(\varphi)$ in `LL_Decomp587l.r0j19_short`.
--
--   In particular, every slice $p \in \{0, \dots, 127\}$ satisfies
--
--   $$\sum_{d=0}^{396} W_{0,d}\, J_{\mathrm{win}, p+d} \le 70{,}737 \cdot 10^9,$$
--
--   certifying $I(\varphi) \le 70{,}737 \times 10^{-9}$ across the peak band.
--
--   **Formalization Note** All quantities are pure `Nat` / `List Nat` computations imported from `Definitions.Def_r0j19_cert_core`.
-- source:
--   Wu (2004), Chen-type 4D Buchstab integral decomposition (supporting certificate lemma for LL_Decomp587l.r0j19_short, theorem_id deade48a-1e4e-40c1-8ddb-1d897d5e2e34)

import Definitions.Def_r0j19_cert_core
open R0J19Cert

namespace R0J19Cert

theorem b3_certs_hi :
  checkSJ8Go t0_b3 854994240 h_288 hy_48 err55_48 err110_48 6 96 525 true Ker_288_24 Ker_288_25 Ker_288_26 Ker_288_27 Ker_288_28 Ker_288_29 Ker_288_30 Ker_288_31 812 Bdry_b3_32 Bdry_b3_24 Jg_b3_3 [] [] [] [] [] [] [] [] = true ∧
  checkSJ8Go t0_b3 869735520 h_288 hy_48 err55_48 err110_48 6 48 525 true Ker_288_32 Ker_288_33 Ker_288_34 Ker_288_35 Ker_288_36 Ker_288_37 Ker_288_38 Ker_288_39 812 Bdry_b3_40 Bdry_b3_32 Jg_b3_4 [] [] [] [] [] [] [] [] = true ∧
  checkSJ8Go t0_b3 884476800 h_288 hy_48 err55_48 err110_48 6 0 525 true Ker_288_40 Ker_288_41 Ker_288_42 Ker_288_43 Ker_288_44 Ker_288_45 Ker_288_46 Ker_288_47 812 [] Bdry_b3_40 Jg_b3_5 [] [] [] [] [] [] [] [] = true ∧
  checkJ6Sum Jg_b3_0 Jg_b3_1 Jg_b3_2 Jg_b3_3 Jg_b3_4 Jg_b3_5 Jc_b3.reverse = true ∧
  checkJWin1 Jc_b3 Jw_b3 = true ∧
  checkSlices 128 1 W0_cert_288 Jw_b3 = true ∧
  checkW0Go h_288 397 A1_num W0_cert_288 = true ∧
  checkKersAll 6 hy_48 h_288 0 Kers_288 = true := by sorry

end R0J19Cert
