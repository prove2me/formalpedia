-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_fft_chirp_arithmetic
-- name    : TaoFivePrimes.rh_high_height_fft_chirp_arithmetic
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T02:26:44.362724+00:00
-- url     : https://prove2.me/theorems/e1fd5bb5-04a8-4509-a72f-6df699be6c62
-- title:
--   TaoFivePrimes.rh_high_height_fft_chirp_arithmetic
-- statement:
--   Exact kernel connection between32767 offset chirp convolution entries and the indexed chirp records. Sequential row traversal avoids repeated global List lookup. Shared by all26 moment orders; no analytic or zero-count assertion.
-- source:
--   Bluestein convolution after Platt DOI10.1090/mcom/3198. Original surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpR
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpI
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpS

theorem TaoFivePrimes.rh_high_height_fft_chirp_arithmetic :
  ∀ c : Nat, c<64 → ∀ j : Nat, j < min 512 (32767-512*c) →
  (let v:=RHHighFFTArithmeticBase.chirp ((512*c+j:Int)-16383).natAbs
   let r:Nat:=(((((RHHighFFTChirpR.rows[c]?).getD [])[j]?).getD 0))
   let i:Nat:=(((((RHHighFFTChirpI.rows[c]?).getD [])[j]?).getD 0))
   let s:Nat:=(((((RHHighFFTChirpS.rows[c]?).getD [])[j]?).getD 0))
   (r:Int)=v.1+2^81 ∧ (i:Int)=v.2+2^81 ∧ s=r+i) := by sorry
