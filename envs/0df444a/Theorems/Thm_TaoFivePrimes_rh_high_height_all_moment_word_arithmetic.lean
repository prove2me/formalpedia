-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_all_moment_word_arithmetic
-- name    : TaoFivePrimes.rh_high_height_all_moment_word_arithmetic
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T07:31:32.260825+00:00
-- url     : https://prove2.me/theorems/1a8b4d32-42e4-4f4a-909e-8a85a92f6784
-- title:
--   TaoFivePrimes.rh_high_height_all_moment_word_arithmetic
-- statement:
--   All16384 proposed sample words decode, in every order0..25, to the actual published rational normalized moment algorithm. Pure aggregation of32 accepted arithmetic packet theorems; no new numerical verification, analytic, sign, count or RH assertion.
-- source:
--   Existing Platt gamma Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighAllMomentWords
import Definitions.Def_TaoFivePrimes_RHHighNormalizedMomentArithmetic
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase

theorem TaoFivePrimes.rh_high_height_all_moment_word_arithmetic :
 ∀ i:Nat,i<16384 → ∀ k:Nat,k<26 →
 RHHighFFTArithmeticBase.decode (RHHighAllMomentWords.word i) k=
 RHHighMomentArithmetic.moment i (RHHighGammaArithmetic.compute i) k := by sorry
