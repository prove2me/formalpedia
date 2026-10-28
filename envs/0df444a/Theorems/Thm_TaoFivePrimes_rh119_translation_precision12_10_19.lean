-- Prove2me | Theorems.Thm_TaoFivePrimes_rh119_translation_precision12_10_19
-- name    : TaoFivePrimes.rh119_translation_precision12_10_19
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T20:31:39.527011+00:00
-- url     : https://prove2.me/theorems/e7b7c0e8-1aa4-4125-b334-e8e8c9af3fc9
-- title:
--   Height-119 rounded translation, degrees 10–19
-- statement:
--   For every degree $10\le n\le19$, let $a_n=N_{238,10^{38},n}/D$ be the exact translated coefficient and let $C_n$ be the stored integer. The exact difference $|a_n-C_n/10^{12}|$ satisfies the applicable degree-dependent tolerance $10^{-12}$ for $n<20$, $10^{-13}$ for $20\le n<25$, $10^{-16}$ for $25\le n<30$, and $10^{-20}$ for $30\le n<40$.
--
--   $$
--   |a_n-C_n/10^{12}|\le\varepsilon_n.
--   $$
--
--   This is an exact arithmetic input to the local xi approximation; its analytic interpretation is separate.
-- source:
--   Exact coefficient translation of the proved 304 moments, using the xi/Taylor framework of sometik179 and theta/Mellin foundations by Gabewhigham; https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a.

import Definitions.Def_TaoFivePrimes_RH304TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RH119RoundedCoefficients12

theorem TaoFivePrimes.rh119_translation_precision12_10_19 : ∀ n : Fin 10,
    let k := 10+n.val
    (if k<20 then (1:ℤ) else if k<25 then 10
      else if k<30 then 10^4 else 10^8) *
      |(10^12:ℤ)*RH304TranslationArithmetic.numerator 238 (10^38) k-
        TaoFivePrimes_RH119RoundedCoefficients12.getD k 0*(RH304TranslationArithmetic.denominator:ℤ)| ≤
          (RH304TranslationArithmetic.denominator:ℤ) := by sorry
