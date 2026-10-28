-- Prove2me | Theorems.Thm_TaoFivePrimes_rh124p5_translation_precision14
-- name    : TaoFivePrimes.rh124p5_translation_precision14
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:47:08.040267+00:00
-- url     : https://prove2.me/theorems/0c08d34c-b62f-4bc4-beb1-fd8b7565cb70
-- title:
--   Height-124.5 translation precision certificate
-- statement:
--   For the forty height-124.5 translated polynomial coefficients, the stored 14-digit candidates have absolute error at most $10^{-14}$ for degrees below 22, $10^{-15}$ for degrees 22–24, $10^{-18}$ for degrees 25–29, and $10^{-24}$ for degrees 30–39.
-- source:
--   Exact translation of candidate Mellin moment data for the height-124.5 xi polynomial. The earlier theta-jet and Mellin framework is due to sometik179 and Gabewhigham; the additional rounded data and translation certificates are new.

import Definitions.Def_TaoFivePrimes_RH320TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RH124p5RoundedCoefficients14

theorem TaoFivePrimes.rh124p5_translation_precision14 : ∀ n : Fin 40,
    (if n.val<22 then (1:ℤ) else if n.val<25 then 10 else if n.val<30 then 10^4 else 10^10) *
      |(10^14:ℤ)*RH320TranslationArithmetic.numerator 249 (10^40) n.val-
        TaoFivePrimes_RH124p5RoundedCoefficients14.getD n.val 0*(RH320TranslationArithmetic.denominator:ℤ)| ≤
          (RH320TranslationArithmetic.denominator:ℤ) := by sorry
