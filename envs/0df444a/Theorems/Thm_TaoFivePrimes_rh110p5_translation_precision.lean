-- Prove2me | Theorems.Thm_TaoFivePrimes_rh110p5_translation_precision
-- name    : TaoFivePrimes.rh110p5_translation_precision
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:19:38.435918+00:00
-- url     : https://prove2.me/theorems/58e4e0e7-ce50-4832-9b54-e8a084889a2d
-- title:
--   Tiered height-110.5 local coefficient translation bounds
-- statement:
--   Let $a_n=N_{221,10^{36},n}/D$ be the exact translated coefficient and let $C_n$ be the stored rounded integer. For $0\le n<40$,
--
--   $$
--   \left|a_n-\frac{C_n}{10^8}\right|\le
--   \begin{cases}10^{-8},&n<20,\\10^{-11},&20\le n<25,\\10^{-16},&25\le n<30,\\10^{-20},&30\le n<40.\end{cases}
--   $$
--
--   This exact arithmetic certificate supports a local xi approximation when combined with separately proved moment enclosures.
-- source:
--   Exact integer translation of the published 256 moment data and 16 extended candidate moments, using the local xi/Taylor framework of sometik179, Prove2Me c9908072-d99a-4431-aad8-a72c6352619a, https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; theta/Mellin foundations by Gabewhigham. The height-110.5 arithmetic data are new.

import Definitions.Def_TaoFivePrimes_RH272TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RH110p5RoundedCoefficients

theorem TaoFivePrimes.rh110p5_translation_precision : ∀ n : Fin 40,
    (if n.val<20 then (1:ℤ) else if n.val<25 then 1000
      else if n.val<30 then 10^8 else 10^12) *
      |(10^8:ℤ)*RH272TranslationArithmetic.numerator 221 (10^36) n.val-
        TaoFivePrimes_RH110p5RoundedCoefficients.getD n.val 0*(RH272TranslationArithmetic.denominator:ℤ)| ≤
          (RH272TranslationArithmetic.denominator:ℤ) := by sorry
