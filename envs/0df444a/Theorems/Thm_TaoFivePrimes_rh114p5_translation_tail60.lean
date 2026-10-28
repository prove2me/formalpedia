-- Prove2me | Theorems.Thm_TaoFivePrimes_rh114p5_translation_tail60
-- name    : TaoFivePrimes.rh114p5_translation_tail60
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:52:47.274757+00:00
-- url     : https://prove2.me/theorems/ec92c74b-8419-4a1e-83ad-a9741ba7387e
-- title:
--   Height-114.5 translated coefficients of degrees 40 through 59
-- statement:
--   Let $a_n=N_{229,10^{37},n}/D$ denote the exact translated coefficient. For each integer $40\le n<60$,
--
--   $$
--   |a_n|\le10^{-32}.
--   $$
--
--   The bound controls the padded tail of the proposed local polynomial. Analytic accuracy requires the separate Mellin moment enclosures.
-- source:
--   Exact integer translation of the published 256 moment data and 48 extended candidate moments, using the local xi/Taylor framework of sometik179, Prove2Me c9908072-d99a-4431-aad8-a72c6352619a, https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; theta/Mellin foundations by Gabewhigham. The height-114.5 arithmetic data are new.

import Definitions.Def_TaoFivePrimes_RH304TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RH114p5RoundedCoefficients

theorem TaoFivePrimes.rh114p5_translation_tail60 : ∀ n : Fin 20,
    (10^32:ℤ)*|RH304TranslationArithmetic.numerator 229 (10^37) (n.val+40)| ≤
      (RH304TranslationArithmetic.denominator:ℤ) := by sorry
