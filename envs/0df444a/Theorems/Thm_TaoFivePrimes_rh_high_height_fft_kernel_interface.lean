-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_fft_kernel_interface
-- name    : TaoFivePrimes.rh_high_height_fft_kernel_interface
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T07:02:38.803637+00:00
-- url     : https://prove2.me/theorems/542f31d6-76b8-46a2-8d72-3fc375090b7a
-- title:
--   TaoFivePrimes.rh_high_height_fft_kernel_interface
-- statement:
--   The shared32767-entry FFT chirp kernel has the exact length, magnitude bounds, centered indexed-chirp identities and pairwise-sum identities used by generic FFT soundness. It joins the accepted row arithmetic to a proved flat-list indexing theorem. No analytic, sign, count or RH claim.
-- source:
--   Bluestein convolution after Platt DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpR
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpI
import Definitions.Def_TaoFivePrimes_RHHighFFTChirpS
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase

theorem TaoFivePrimes.rh_high_height_fft_kernel_interface :
 (∀rows∈[RHHighFFTChirpR.rows,RHHighFFTChirpI.rows,RHHighFFTChirpS.rows],rows.flatten.length=32767) ∧
 RHHighFFTChirpR.rows.flatten.all (fun x=>decide (x≤2^82))=true ∧
 RHHighFFTChirpI.rows.flatten.all (fun x=>decide (x≤2^82))=true ∧
 (∀i:Nat,i<32767 →
    ((((RHHighFFTChirpR.rows.flatten[i]?).getD 0:Nat):Int)-2^81,
      (((RHHighFFTChirpI.rows.flatten[i]?).getD 0:Nat):Int)-2^81)=
       RHHighFFTArithmeticBase.chirp ((i:Int)-16383).natAbs ∧
    ((RHHighFFTChirpS.rows.flatten[i]?).getD 0)=
      ((RHHighFFTChirpR.rows.flatten[i]?).getD 0)+((RHHighFFTChirpI.rows.flatten[i]?).getD 0)) := by sorry
