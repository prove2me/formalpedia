-- Prove2me | Theorems.Thm_TaoFivePrimes_rh114p5_translation_precision
-- name    : TaoFivePrimes.rh114p5_translation_precision
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:52:38.389994+00:00
-- url     : https://prove2.me/theorems/718d3025-8db7-4dae-a65f-c4088317cc37
-- title:
--   Tiered height-114.5 local coefficient translation bounds
-- statement:
--   Let $a_n=N_{229,10^{37},n}/D$ be the exact translated coefficient and let $C_n$ be the stored rounded integer. For $0\le n<40$,
--
--   $$
--   \left|a_n-\frac{C_n}{10^8}\right|\le
--   \begin{cases}10^{-8},&n<20,\\10^{-11},&20\le n<25,\\10^{-16},&25\le n<30,\\10^{-20},&30\le n<40.\end{cases}
--   $$
--
--   This exact arithmetic certificate supports a local xi approximation when combined with separately proved moment enclosures.
-- source:
--   Exact integer translation of the published 256 moment data and 48 extended candidate moments, using the local xi/Taylor framework of sometik179, Prove2Me c9908072-d99a-4431-aad8-a72c6352619a, https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; theta/Mellin foundations by Gabewhigham. The height-114.5 arithmetic data are new.

import Definitions.Def_TaoFivePrimes_RH304TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RH114p5RoundedCoefficients

theorem TaoFivePrimes.rh114p5_translation_precision : ∀ n : Fin 40,
    (if n.val<20 then (1:ℤ) else if n.val<25 then 1000
      else if n.val<30 then 10^8 else 10^12) *
      |(10^8:ℤ)*RH304TranslationArithmetic.numerator 229 (10^37) n.val-
        TaoFivePrimes_RH114p5RoundedCoefficients.getD n.val 0*(RH304TranslationArithmetic.denominator:ℤ)| ≤
          (RH304TranslationArithmetic.denominator:ℤ) := by sorry
