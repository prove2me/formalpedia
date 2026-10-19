-- Prove2me | Theorems.Thm_TaoFivePrimes_fft_input_bounds_chunk1
-- name    : TaoFivePrimes.fft_input_bounds_chunk1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-18T14:27:25.77245+00:00
-- url     : https://prove2.me/theorems/952c406a-eaa3-4aab-a077-1b8d4fc16f75
-- title:
--   Gamma-FFT input matrices, chunk 1: shape and magnitude bounds
-- statement:
--   Each of the 7 gamma-FFT input matrices in chunk 1 has exactly 16384 entries when flattened, every row has length 512, and every entry is at most $2^{167}$. This is a finite certificate check on explicitly stored data, split from the whole 52-matrix statement so that each chunk can be compiled and cached on its own.
-- source:
--   Certificate data and statement: the TaoFivePrimes development (T. Tao, Every odd number greater than 1 is the sum of at most five primes, Math. Comp. 83 (2014), 997-1038); this chunk lemma is a compilation-size split of the platform theorem TaoFivePrimes.rh_high_height_gamma_fft_array_bounds.

import Definitions.Def_TaoFivePrimes_RHHighFFTInputI03
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR04
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI04
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR05
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI05
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR06
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI06

namespace TaoFivePrimes

theorem fft_input_bounds_chunk1 :
  ∀ rows ∈ [RHHighFFTInputI03.rows,RHHighFFTInputR04.rows,RHHighFFTInputI04.rows,RHHighFFTInputR05.rows,RHHighFFTInputI05.rows,RHHighFFTInputR06.rows,RHHighFFTInputI06.rows],rows.flatten.length=16384 ∧ rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤2^167)))=true := by sorry

end TaoFivePrimes
