-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_all_moment_word_arithmetic
-- name    : TaoFivePrimes.rh_batch01_height_all_moment_word_arithmetic
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T22:04:23.371191+00:00
-- url     : https://prove2.me/theorems/e2f71956-2ea3-4cfa-a333-c7f5598b29c8
-- title:
--   TaoFivePrimes.rh_batch01_height_all_moment_word_arithmetic
-- statement:
--   All16384 proposed sample words decode, in every order0..25, to the actual published rational normalized moment algorithm. Pure aggregation of32 accepted arithmetic packet theorems; no new numerical verification, analytic, sign, count or RH assertion.
-- source:
--   Existing Platt gamma Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01AllMomentWords
import Definitions.Def_TaoFivePrimes_RHBatch01NormalizedMomentArithmetic
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase

theorem TaoFivePrimes.rh_batch01_height_all_moment_word_arithmetic :
 ∀ i:Nat,i<16384 → ∀ k:Nat,k<26 →
 RHHighFFTArithmeticBase.decode (RHBatch01AllMomentWords.word i) k=
 RHBatch01MomentArithmetic.moment i (RHBatch01GammaArithmetic.compute i) k := by sorry
