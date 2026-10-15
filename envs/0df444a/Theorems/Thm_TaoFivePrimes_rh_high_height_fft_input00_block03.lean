-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_fft_input00_block03
-- name    : TaoFivePrimes.rh_high_height_fft_input00_block03
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T02:46:59.431552+00:00
-- url     : https://prove2.me/theorems/a6d12297-8e42-46dd-8c3d-72c0555fd4d9
-- title:
--   TaoFivePrimes.rh_high_height_fft_input00_block03
-- statement:
--   Exact kernel connection between2048 offset FFT input pairs and chirped moment words, order0, globalindices6144 through8191. The statement imports four moment data packets, keeping server compilation bounded. No analytic, sign or zero-count claim.
-- source:
--   Bluestein convolution after Platt DOI10.1090/mcom/3198. Original surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighFFTMomentBlock03
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR00
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI00

theorem TaoFivePrimes.rh_high_height_fft_input00_block03 :
  ∀ i : Nat, i<2048 → RHHighFFTArithmeticBase.raw (RHHighFFTMomentBlock03.word i) 0 (6144+i)=(let r:Nat:=(((RHHighFFTInputR00.rows[(6144+i)/512]?).getD [])[(6144+i)%512]?).getD 0
   let v:Nat:=(((RHHighFFTInputI00.rows[(6144+i)/512]?).getD [])[(6144+i)%512]?).getD 0
   ((r:Int)-2^166,(v:Int)-2^166)) := by sorry
