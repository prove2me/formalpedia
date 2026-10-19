-- Prove2me | Theorems.Thm_TaoFivePrimes_fft_input_bounds_chunk6
-- name    : TaoFivePrimes.fft_input_bounds_chunk6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-18T14:27:23.329589+00:00
-- url     : https://prove2.me/theorems/3a320de5-9e41-46e0-b947-4aeb0c453352
-- title:
--   Gamma-FFT input matrices, chunk 6: shape and magnitude bounds
-- statement:
--   Each of the 6 gamma-FFT input matrices in chunk 6 has exactly 16384 entries when flattened, every row has length 512, and every entry is at most $2^{167}$. This is a finite certificate check on explicitly stored data, split from the whole 52-matrix statement so that each chunk can be compiled and cached on its own.
-- source:
--   Certificate data and statement: the TaoFivePrimes development (T. Tao, Every odd number greater than 1 is the sum of at most five primes, Math. Comp. 83 (2014), 997-1038); this chunk lemma is a compilation-size split of the platform theorem TaoFivePrimes.rh_high_height_gamma_fft_array_bounds.

import Definitions.Def_TaoFivePrimes_RHHighFFTInputR20
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI20
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR21
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI21
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR22
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI22

namespace TaoFivePrimes

theorem fft_input_bounds_chunk6 :
  ∀ rows ∈ [RHHighFFTInputR20.rows,RHHighFFTInputI20.rows,RHHighFFTInputR21.rows,RHHighFFTInputI21.rows,RHHighFFTInputR22.rows,RHHighFFTInputI22.rows],rows.flatten.length=16384 ∧ rows.all (fun row=>decide (row.length=512) && row.all (fun x=>decide (x≤2^167)))=true := by sorry

end TaoFivePrimes
