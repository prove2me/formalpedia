-- Prove2me | Theorems.Thm_TaoFivePrimes_fft_input_bounds_chunk4
-- name    : TaoFivePrimes.fft_input_bounds_chunk4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-18T14:27:24.748605+00:00
-- url     : https://prove2.me/theorems/c7fb03d7-bbee-4f43-a938-2fb8da981e81
-- title:
--   Gamma-FFT input matrices, chunk 4: shape and magnitude bounds
-- statement:
--   Each of the 6 gamma-FFT input matrices in chunk 4 has exactly 16384 entries when flattened, every row has length 512, and every entry is at most $2^{167}$. This is a finite certificate check on explicitly stored data, split from the whole 52-matrix statement so that each chunk can be compiled and cached on its own.
-- source:
--   Certificate data and statement: the TaoFivePrimes development (T. Tao, Every odd number greater than 1 is the sum of at most five primes, Math. Comp. 83 (2014), 997-1038); this chunk lemma is a compilation-size split of the platform theorem TaoFivePrimes.rh_high_height_gamma_fft_array_bounds.

import Definitions.Def_TaoFivePrimes_RHHighFFTInputR14
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI14
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR15
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI15
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR16
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI16

namespace TaoFivePrimes

theorem fft_input_bounds_chunk4 :
  ∀ rows ∈ [RHHighFFTInputR14.rows,RHHighFFTInputI14.rows,RHHighFFTInputR15.rows,RHHighFFTInputI15.rows,RHHighFFTInputR16.rows,RHHighFFTInputI16.rows],rows.flatten.length=16384 ∧ rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤2^167)))=true := by sorry

end TaoFivePrimes
