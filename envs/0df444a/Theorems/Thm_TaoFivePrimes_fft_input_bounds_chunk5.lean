-- Prove2me | Theorems.Thm_TaoFivePrimes_fft_input_bounds_chunk5
-- name    : TaoFivePrimes.fft_input_bounds_chunk5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-18T14:27:20.722933+00:00
-- url     : https://prove2.me/theorems/83aecdf6-42ce-4ebf-b1e7-d6a3eeb5295f
-- title:
--   Gamma-FFT input matrices, chunk 5: shape and magnitude bounds
-- statement:
--   Each of the 6 gamma-FFT input matrices in chunk 5 has exactly 16384 entries when flattened, every row has length 512, and every entry is at most $2^{167}$. This is a finite certificate check on explicitly stored data, split from the whole 52-matrix statement so that each chunk can be compiled and cached on its own.
-- source:
--   Certificate data and statement: the TaoFivePrimes development (T. Tao, Every odd number greater than 1 is the sum of at most five primes, Math. Comp. 83 (2014), 997-1038); this chunk lemma is a compilation-size split of the platform theorem TaoFivePrimes.rh_high_height_gamma_fft_array_bounds.

import Definitions.Def_TaoFivePrimes_RHHighFFTInputR17
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI17
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR18
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI18
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR19
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI19

namespace TaoFivePrimes

theorem fft_input_bounds_chunk5 :
  ∀ rows ∈ [RHHighFFTInputR17.rows,RHHighFFTInputI17.rows,RHHighFFTInputR18.rows,RHHighFFTInputI18.rows,RHHighFFTInputR19.rows,RHHighFFTInputI19.rows],rows.flatten.length=16384 ∧ rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤2^167)))=true := by sorry

end TaoFivePrimes
