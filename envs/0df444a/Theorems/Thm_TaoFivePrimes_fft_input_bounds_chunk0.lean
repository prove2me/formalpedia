-- Prove2me | Theorems.Thm_TaoFivePrimes_fft_input_bounds_chunk0
-- name    : TaoFivePrimes.fft_input_bounds_chunk0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-18T14:27:18.12585+00:00
-- url     : https://prove2.me/theorems/fea211a6-8193-4bcd-bf1b-ee4163573391
-- title:
--   Gamma-FFT input matrices, chunk 0: shape and magnitude bounds
-- statement:
--   Each of the 7 gamma-FFT input matrices in chunk 0 has exactly 16384 entries when flattened, every row has length 512, and every entry is at most $2^{167}$. This is a finite certificate check on explicitly stored data, split from the whole 52-matrix statement so that each chunk can be compiled and cached on its own.
-- source:
--   Certificate data and statement: the TaoFivePrimes development (T. Tao, Every odd number greater than 1 is the sum of at most five primes, Math. Comp. 83 (2014), 997-1038); this chunk lemma is a compilation-size split of the platform theorem TaoFivePrimes.rh_high_height_gamma_fft_array_bounds.

import Definitions.Def_TaoFivePrimes_RHHighFFTInputR00
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI00
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR01
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI01
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR02
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI02
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR03

namespace TaoFivePrimes

theorem fft_input_bounds_chunk0 :
  ∀ rows ∈ [RHHighFFTInputR00.rows,RHHighFFTInputI00.rows,RHHighFFTInputR01.rows,RHHighFFTInputI01.rows,RHHighFFTInputR02.rows,RHHighFFTInputI02.rows,RHHighFFTInputR03.rows],rows.flatten.length=16384 ∧ rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤2^167)))=true := by sorry

end TaoFivePrimes
