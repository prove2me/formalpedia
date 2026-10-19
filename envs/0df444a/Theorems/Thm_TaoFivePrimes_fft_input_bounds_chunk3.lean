-- Prove2me | Theorems.Thm_TaoFivePrimes_fft_input_bounds_chunk3
-- name    : TaoFivePrimes.fft_input_bounds_chunk3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-18T14:27:19.95772+00:00
-- url     : https://prove2.me/theorems/7a1b924c-cd45-4aa7-bdb0-0220a9935704
-- title:
--   Gamma-FFT input matrices, chunk 3: shape and magnitude bounds
-- statement:
--   Each of the 7 gamma-FFT input matrices in chunk 3 has exactly 16384 entries when flattened, every row has length 512, and every entry is at most $2^{167}$. This is a finite certificate check on explicitly stored data, split from the whole 52-matrix statement so that each chunk can be compiled and cached on its own.
-- source:
--   Certificate data and statement: the TaoFivePrimes development (T. Tao, Every odd number greater than 1 is the sum of at most five primes, Math. Comp. 83 (2014), 997-1038); this chunk lemma is a compilation-size split of the platform theorem TaoFivePrimes.rh_high_height_gamma_fft_array_bounds.

import Definitions.Def_TaoFivePrimes_RHHighFFTInputI10
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR11
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI11
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR12
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI12
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR13
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI13

namespace TaoFivePrimes

theorem fft_input_bounds_chunk3 :
  ∀ rows ∈ [RHHighFFTInputI10.rows,RHHighFFTInputR11.rows,RHHighFFTInputI11.rows,RHHighFFTInputR12.rows,RHHighFFTInputI12.rows,RHHighFFTInputR13.rows,RHHighFFTInputI13.rows],rows.flatten.length=16384 ∧ rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤2^167)))=true := by sorry

end TaoFivePrimes
