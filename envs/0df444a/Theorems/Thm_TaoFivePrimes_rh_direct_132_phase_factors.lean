-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_direct_132_phase_factors
-- name    : TaoFivePrimes.rh_direct_132_phase_factors
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:59:41.724707+00:00
-- url     : https://prove2.me/theorems/5eac3c24-b040-458f-b08f-01dcc6d96c53
-- title:
--   Exact integer phase Taylor factors
-- statement:
--   For the published integer list $F_\ell$ and each $0\le\ell<184$,
--
--   $$
--   F_\ell=99^\ell 8^{183-\ell}\frac{183!}{\ell!}.
--   $$
--
--   This exact arithmetic identity supplies a common denominator for the height-132 phase Taylor coefficients.
-- source:
--   Exact phase convolution built on the published theta-jet correlation data of sometik179, with theta/Mellin foundations due to Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHDirect132PhaseFactors
import Mathlib

theorem TaoFivePrimes.rh_direct_132_phase_factors : ∀ l : Fin 184,
    TaoFivePrimes_RHDirect132PhaseFactors.getD l.val 0 =
      99^l.val * 8^(183-l.val) * ((183:ℕ).factorial/(l.val.factorial)) := by sorry
