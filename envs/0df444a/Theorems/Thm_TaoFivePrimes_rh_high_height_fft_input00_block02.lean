-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_fft_input00_block02
-- name    : TaoFivePrimes.rh_high_height_fft_input00_block02
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T02:34:29.607877+00:00
-- url     : https://prove2.me/theorems/2bfd1a0d-c549-4454-acd6-f2cdb6c18adb
-- title:
--   TaoFivePrimes.rh_high_height_fft_input00_block02
-- statement:
--   Exact kernel connection between2048 offset FFT input pairs and chirped moment words, order0, globalindices4096 through6143. The statement imports four moment data packets, keeping server compilation bounded. No analytic, sign or zero-count claim.
-- source:
--   Bluestein convolution after Platt DOI10.1090/mcom/3198. Original surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighFFTMomentBlock02
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR00
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI00

theorem TaoFivePrimes.rh_high_height_fft_input00_block02 :
  ∀ i : Nat, i<2048 → RHHighFFTArithmeticBase.raw (RHHighFFTMomentBlock02.word i) 0 (4096+i)=(let r:Nat:=(((RHHighFFTInputR00.rows[(4096+i)/512]?).getD [])[(4096+i)%512]?).getD 0
   let v:Nat:=(((RHHighFFTInputI00.rows[(4096+i)/512]?).getD [])[(4096+i)%512]?).getD 0
   ((r:Int)-2^166,(v:Int)-2^166)) := by sorry
