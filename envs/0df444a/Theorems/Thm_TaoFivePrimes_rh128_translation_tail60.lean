-- Prove2me | Theorems.Thm_TaoFivePrimes_rh128_translation_tail60
-- name    : TaoFivePrimes.rh128_translation_tail60
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:10:21.628988+00:00
-- url     : https://prove2.me/theorems/54407ed5-d9ad-4d84-b69a-6e0bbc5b611a
-- title:
--   Height-128 translation tail certificate
-- statement:
--   The absolute values of the translated polynomial coefficients of degrees 40 through 59 are at most $10^{-32}$.
-- source:
--   Exact translation of candidate Mellin moment data for the height-128 xi polynomial. The earlier theta-jet and Mellin framework is due to sometik179 and Gabewhigham; the additional rounded data and translation certificates are new.

import Definitions.Def_TaoFivePrimes_RH336TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RH128RoundedCoefficients14

theorem TaoFivePrimes.rh128_translation_tail60 : ∀ n : Fin 20,
    (10^32:ℤ)*|RH336TranslationArithmetic.numerator 256 (10^41) (n.val+40)| ≤
      (RH336TranslationArithmetic.denominator:ℤ) := by sorry
