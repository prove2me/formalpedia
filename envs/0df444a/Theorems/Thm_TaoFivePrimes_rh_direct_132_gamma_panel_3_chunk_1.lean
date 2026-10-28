-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_direct_132_gamma_panel_3_chunk_1
-- name    : TaoFivePrimes.rh_direct_132_gamma_panel_3_chunk_1
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:09:21.060167+00:00
-- url     : https://prove2.me/theorems/04d530d0-b104-4ac5-9d82-a7169effd983
-- title:
--   Height-132 phase correlations: panel 3, indices 20–39
-- statement:
--   For panel index $i=3$, let $\Gamma_{i,m}$ be the published finite Gaussian-integer phase convolution, and let $G_{i,m}$ be its stored candidate value. For all $m\in[20,39]$,
--
--   $$
--   G_{i,m}=\Gamma_{i,m}.
--   $$
--
--   This is an exact arithmetic certificate for twenty coefficients of one panel; its relation to the quadrature rule is separate.
-- source:
--   Exact phase convolution built on the published theta-jet correlation data of sometik179, with theta/Mellin foundations due to Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHDirect132Integer
import Definitions.Def_TaoFivePrimes_RHDirect132GammaData0
import Mathlib

theorem TaoFivePrimes.rh_direct_132_gamma_panel_3_chunk_1 : ∀ m : Fin 20,
    (RHDirect132Integer.gammaRe 3 (20+m.val),
      RHDirect132Integer.gammaIm 3 (20+m.val)) =
      ((TaoFivePrimes_RHDirect132GammaData0.getD 3 []).getD (20+m.val) (0,0)) := by sorry
