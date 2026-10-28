-- Prove2me | Theorems.Thm_TaoFivePrimes_rh124p5_translation_tail60
-- name    : TaoFivePrimes.rh124p5_translation_tail60
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:46:53.535574+00:00
-- url     : https://prove2.me/theorems/1282f4f3-0cf6-4dea-a82e-fd979b2d4b9c
-- title:
--   Height-124.5 translation tail certificate
-- statement:
--   The absolute values of the translated polynomial coefficients of degrees 40 through 59 are at most $10^{-32}$.
-- source:
--   Exact translation of candidate Mellin moment data for the height-124.5 xi polynomial. The earlier theta-jet and Mellin framework is due to sometik179 and Gabewhigham; the additional rounded data and translation certificates are new.

import Definitions.Def_TaoFivePrimes_RH320TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RH124p5RoundedCoefficients14

theorem TaoFivePrimes.rh124p5_translation_tail60 : ∀ n : Fin 20,
    (10^32:ℤ)*|RH320TranslationArithmetic.numerator 249 (10^40) (n.val+40)| ≤
      (RH320TranslationArithmetic.denominator:ℤ) := by sorry
