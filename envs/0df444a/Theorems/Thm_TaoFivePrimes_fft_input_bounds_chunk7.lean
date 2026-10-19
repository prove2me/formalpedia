-- Prove2me | Theorems.Thm_TaoFivePrimes_fft_input_bounds_chunk7
-- name    : TaoFivePrimes.fft_input_bounds_chunk7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-18T14:27:17.597129+00:00
-- url     : https://prove2.me/theorems/5de723f2-90da-4d99-8f0b-62a106bb0970
-- title:
--   Gamma-FFT input matrices, chunk 7: shape and magnitude bounds
-- statement:
--   Each of the 6 gamma-FFT input matrices in chunk 7 has exactly 16384 entries when flattened, every row has length 512, and every entry is at most $2^{167}$. This is a finite certificate check on explicitly stored data, split from the whole 52-matrix statement so that each chunk can be compiled and cached on its own.
-- source:
--   Certificate data and statement: the TaoFivePrimes development (T. Tao, Every odd number greater than 1 is the sum of at most five primes, Math. Comp. 83 (2014), 997-1038); this chunk lemma is a compilation-size split of the platform theorem TaoFivePrimes.rh_high_height_gamma_fft_array_bounds.

import Definitions.Def_TaoFivePrimes_RHHighFFTInputR23
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI23
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR24
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI24
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR25
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI25

namespace TaoFivePrimes

theorem fft_input_bounds_chunk7 :
  ∀ rows ∈ [RHHighFFTInputR23.rows,RHHighFFTInputI23.rows,RHHighFFTInputR24.rows,RHHighFFTInputI24.rows,RHHighFFTInputR25.rows,RHHighFFTInputI25.rows],rows.flatten.length=16384 ∧ rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤2^167)))=true := by sorry

end TaoFivePrimes
