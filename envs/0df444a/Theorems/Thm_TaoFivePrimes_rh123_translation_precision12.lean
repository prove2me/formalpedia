-- Prove2me | Theorems.Thm_TaoFivePrimes_rh123_translation_precision12
-- name    : TaoFivePrimes.rh123_translation_precision12
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:35:37.228662+00:00
-- url     : https://prove2.me/theorems/13792117-1ff6-4210-a697-3509bece5557
-- title:
--   Height-123 translation precision certificate
-- statement:
--   For the forty height-123 translated polynomial coefficients, the stored 12-digit candidates have absolute error at most $10^{-12}$ for degrees below 20, $10^{-13}$ for degrees 20–24, $10^{-16}$ for degrees 25–29, and $10^{-20}$ for degrees 30–39.
-- source:
--   Exact translation of candidate Mellin moment data for the height-123 xi polynomial. The earlier theta-jet and Mellin framework is due to sometik179 and Gabewhigham; the additional rounded data and translation certificates are new.

import Definitions.Def_TaoFivePrimes_RH320TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RH123RoundedCoefficients12

theorem TaoFivePrimes.rh123_translation_precision12 : ∀ n : Fin 40,
    (if n.val<20 then (1:ℤ) else if n.val<25 then 10 else if n.val<30 then 10^4 else 10^8) *
      |(10^12:ℤ)*RH320TranslationArithmetic.numerator 246 (10^40) n.val-
        TaoFivePrimes_RH123RoundedCoefficients12.getD n.val 0*(RH320TranslationArithmetic.denominator:ℤ)| ≤
          (RH320TranslationArithmetic.denominator:ℤ) := by sorry
