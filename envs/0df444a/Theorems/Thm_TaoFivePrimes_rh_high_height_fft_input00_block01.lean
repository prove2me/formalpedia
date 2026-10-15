-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_fft_input00_block01
-- name    : TaoFivePrimes.rh_high_height_fft_input00_block01
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T02:39:15.664985+00:00
-- url     : https://prove2.me/theorems/a6a4da4a-300c-4747-9bc9-1821f6b02bf2
-- title:
--   TaoFivePrimes.rh_high_height_fft_input00_block01
-- statement:
--   Exact kernel connection between2048 offset FFT input pairs and chirped moment words, order0, globalindices2048 through4095. The statement imports four moment data packets, keeping server compilation bounded. No analytic, sign or zero-count claim.
-- source:
--   Bluestein convolution after Platt DOI10.1090/mcom/3198. Original surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighFFTMomentBlock01
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR00
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI00

theorem TaoFivePrimes.rh_high_height_fft_input00_block01 :
  ∀ i : Nat, i<2048 → RHHighFFTArithmeticBase.raw (RHHighFFTMomentBlock01.word i) 0 (2048+i)=(let r:Nat:=(((RHHighFFTInputR00.rows[(2048+i)/512]?).getD [])[(2048+i)%512]?).getD 0
   let v:Nat:=(((RHHighFFTInputI00.rows[(2048+i)/512]?).getD [])[(2048+i)%512]?).getD 0
   ((r:Int)-2^166,(v:Int)-2^166)) := by sorry
