-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_direct_132_gamma_panel_8_chunk_2
-- name    : TaoFivePrimes.rh_direct_132_gamma_panel_8_chunk_2
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:09:24.243313+00:00
-- url     : https://prove2.me/theorems/a44e5322-3ca1-46f3-97dc-b20a961b8c77
-- title:
--   Height-132 phase correlations: panel 8, indices 40–59
-- statement:
--   For panel index $i=8$, let $\Gamma_{i,m}$ be the published finite Gaussian-integer phase convolution, and let $G_{i,m}$ be its stored candidate value. For all $m\in[40,59]$,
--
--   $$
--   G_{i,m}=\Gamma_{i,m}.
--   $$
--
--   This is an exact arithmetic certificate for twenty coefficients of one panel; its relation to the quadrature rule is separate.
-- source:
--   Exact phase convolution built on the published theta-jet correlation data of sometik179, with theta/Mellin foundations due to Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHDirect132Integer
import Definitions.Def_TaoFivePrimes_RHDirect132GammaData2
import Mathlib

theorem TaoFivePrimes.rh_direct_132_gamma_panel_8_chunk_2 : ∀ m : Fin 20,
    (RHDirect132Integer.gammaRe 8 (40+m.val),
      RHDirect132Integer.gammaIm 8 (40+m.val)) =
      ((TaoFivePrimes_RHDirect132GammaData2.getD 0 []).getD (40+m.val) (0,0)) := by sorry
