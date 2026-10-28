-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_direct_132_gamma_panel_8
-- name    : TaoFivePrimes.rh_direct_132_gamma_panel_8
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:01:53.321745+00:00
-- url     : https://prove2.me/theorems/21672f44-05f3-4e2b-9041-c749006bf42c
-- title:
--   Exact height-132 phase correlations for panel 8
-- statement:
--   For panel index $i=8$, let $\Gamma_{i,m}$ be the published finite Gaussian-integer phase convolution, and let $G_{i,m}$ be its stored candidate value. For each $0\le m<60$,
--
--   $$
--   G_{i,m}=\Gamma_{i,m}.
--   $$
--
--   This is an exact arithmetic certificate for one panel; its relation to the quadrature rule is separate.
-- source:
--   Exact phase convolution built on the published theta-jet correlation data of sometik179, with theta/Mellin foundations due to Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHDirect132Integer
import Definitions.Def_TaoFivePrimes_RHDirect132GammaData2
import Mathlib

theorem TaoFivePrimes.rh_direct_132_gamma_panel_8 : ∀ m : Fin 60,
    (RHDirect132Integer.gammaRe 8 m.val, RHDirect132Integer.gammaIm 8 m.val) =
      ((TaoFivePrimes_RHDirect132GammaData2.getD 0 []).getD m.val (0,0)) := by sorry
