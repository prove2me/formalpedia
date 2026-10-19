-- Prove2me | Theorems.Thm_TaoFivePrimes_fft_input_bounds_chunk2
-- name    : TaoFivePrimes.fft_input_bounds_chunk2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-18T14:27:10.636135+00:00
-- url     : https://prove2.me/theorems/a2d206f5-3b25-4362-bb97-269a53a51c52
-- title:
--   Gamma-FFT input matrices, chunk 2: shape and magnitude bounds
-- statement:
--   Each of the 7 gamma-FFT input matrices in chunk 2 has exactly 16384 entries when flattened, every row has length 512, and every entry is at most $2^{167}$. This is a finite certificate check on explicitly stored data, split from the whole 52-matrix statement so that each chunk can be compiled and cached on its own.
-- source:
--   Certificate data and statement: the TaoFivePrimes development (T. Tao, Every odd number greater than 1 is the sum of at most five primes, Math. Comp. 83 (2014), 997-1038); this chunk lemma is a compilation-size split of the platform theorem TaoFivePrimes.rh_high_height_gamma_fft_array_bounds.

import Definitions.Def_TaoFivePrimes_RHHighFFTInputR07
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI07
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR08
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI08
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR09
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI09
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR10

namespace TaoFivePrimes

theorem fft_input_bounds_chunk2 :
  ∀ rows ∈ [RHHighFFTInputR07.rows,RHHighFFTInputI07.rows,RHHighFFTInputR08.rows,RHHighFFTInputI08.rows,RHHighFFTInputR09.rows,RHHighFFTInputI09.rows,RHHighFFTInputR10.rows],rows.flatten.length=16384 ∧ rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤2^167)))=true := by sorry

end TaoFivePrimes
