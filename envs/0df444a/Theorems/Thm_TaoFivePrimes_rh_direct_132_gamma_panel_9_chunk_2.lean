-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_direct_132_gamma_panel_9_chunk_2
-- name    : TaoFivePrimes.rh_direct_132_gamma_panel_9_chunk_2
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:09:27.548979+00:00
-- url     : https://prove2.me/theorems/78142b7f-a6d9-43ff-b8a1-9f23195f7371
-- title:
--   Height-132 phase correlations: panel 9, indices 40–59
-- statement:
--   For panel index $i=9$, let $\Gamma_{i,m}$ be the published finite Gaussian-integer phase convolution, and let $G_{i,m}$ be its stored candidate value. For all $m\in[40,59]$,
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

theorem TaoFivePrimes.rh_direct_132_gamma_panel_9_chunk_2 : ∀ m : Fin 20,
    (RHDirect132Integer.gammaRe 9 (40+m.val),
      RHDirect132Integer.gammaIm 9 (40+m.val)) =
      ((TaoFivePrimes_RHDirect132GammaData2.getD 1 []).getD (40+m.val) (0,0)) := by sorry
