-- Prove2me | Theorems.Thm_TaoFivePrimes_rh119_translation_tail60
-- name    : TaoFivePrimes.rh119_translation_tail60
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T20:23:50.825935+00:00
-- url     : https://prove2.me/theorems/82ce8b54-dfae-4cee-858f-ef2fcd524823
-- title:
--   Height-119 translated coefficients of degrees 40 through 59
-- statement:
--   Let $a_n=N_{238,10^{38},n}/D$ be the exact translated coefficient. For each integer $40\le n<60$,
--
--   $$
--   |a_n|\le10^{-32}.
--   $$
--
--   This bounds the zero-padded tail of the proposed local polynomial. It does not alone provide an analytic xi approximation.
-- source:
--   Exact integer translation of the proved 304 Mellin-moment candidates, using the xi/Taylor framework of sometik179, https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; theta/Mellin foundations are due to Gabewhigham. The height-119 and 10^12-denominator data are new.

import Definitions.Def_TaoFivePrimes_RH304TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RH119RoundedCoefficients12

theorem TaoFivePrimes.rh119_translation_tail60 : ∀ n : Fin 20,
    (10^32:ℤ)*|RH304TranslationArithmetic.numerator 238 (10^38) (n.val+40)| ≤
      (RH304TranslationArithmetic.denominator:ℤ) := by sorry
