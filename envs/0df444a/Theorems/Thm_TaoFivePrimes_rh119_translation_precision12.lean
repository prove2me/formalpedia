-- Prove2me | Theorems.Thm_TaoFivePrimes_rh119_translation_precision12
-- name    : TaoFivePrimes.rh119_translation_precision12
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T20:23:42.878026+00:00
-- url     : https://prove2.me/theorems/b21604cc-4851-49e6-986f-8c6e9eec02ad
-- title:
--   Tiered height-119 coefficient translation with 12-digit rounding
-- statement:
--   Let $a_n=N_{238,10^{38},n}/D$ be the exact translated coefficient and let $C_n$ be the stored rounded integer. For $0\le n<40$,
--
--   $$
--   \left|a_n-\frac{C_n}{10^{12}}\right|\le
--   \begin{cases}10^{-12},&n<20,\\10^{-13},&20\le n<25,\\10^{-16},&25\le n<30,\\10^{-20},&30\le n<40.\end{cases}
--   $$
--
--   This arithmetic certificate supports an analytic xi approximation when combined with the separately proved moment enclosures.
-- source:
--   Exact integer translation of the proved 304 Mellin-moment candidates, using the xi/Taylor framework of sometik179, https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; theta/Mellin foundations are due to Gabewhigham. The height-119 and 10^12-denominator data are new.

import Definitions.Def_TaoFivePrimes_RH304TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RH119RoundedCoefficients12

theorem TaoFivePrimes.rh119_translation_precision12 : ∀ n : Fin 40,
    (if n.val<20 then (1:ℤ) else if n.val<25 then 10
      else if n.val<30 then 10^4 else 10^8) *
      |(10^12:ℤ)*RH304TranslationArithmetic.numerator 238 (10^38) n.val-
        TaoFivePrimes_RH119RoundedCoefficients12.getD n.val 0*(RH304TranslationArithmetic.denominator:ℤ)| ≤
          (RH304TranslationArithmetic.denominator:ℤ) := by sorry
