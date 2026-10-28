-- Prove2me | Theorems.Thm_TaoFivePrimes_rh128_translation_precision14
-- name    : TaoFivePrimes.rh128_translation_precision14
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:10:16.70468+00:00
-- url     : https://prove2.me/theorems/a308c539-fa75-402f-be73-ac10d04fd069
-- title:
--   Height-128 translation precision certificate
-- statement:
--   For the forty height-128 translated polynomial coefficients, the stored 14-digit candidates have absolute error at most $10^{-14}$ for degrees below 22, $2\cdot10^{-15}$ for degrees 22–24, $10^{-18}$ for degrees 25–29, and $10^{-24}$ for degrees 30–39.
-- source:
--   Exact translation of candidate Mellin moment data for the height-128 xi polynomial. The earlier theta-jet and Mellin framework is due to sometik179 and Gabewhigham; the additional rounded data and translation certificates are new.

import Definitions.Def_TaoFivePrimes_RH336TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RH128RoundedCoefficients14

theorem TaoFivePrimes.rh128_translation_precision14 : ∀ n : Fin 40,
    (if n.val<22 then (1:ℤ) else if n.val<25 then 5 else if n.val<30 then 10^4 else 10^10) *
      |(10^14:ℤ)*RH336TranslationArithmetic.numerator 256 (10^41) n.val-
        TaoFivePrimes_RH128RoundedCoefficients14.getD n.val 0*(RH336TranslationArithmetic.denominator:ℤ)| ≤
          (RH336TranslationArithmetic.denominator:ℤ) := by sorry
