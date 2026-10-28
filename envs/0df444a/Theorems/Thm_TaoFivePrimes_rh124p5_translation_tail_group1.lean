-- Prove2me | Theorems.Thm_TaoFivePrimes_rh124p5_translation_tail_group1
-- name    : TaoFivePrimes.rh124p5_translation_tail_group1
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:46:53.994432+00:00
-- url     : https://prove2.me/theorems/4a83e90f-ed32-4012-bc75-2f0bfb4be6a2
-- title:
--   Height-124.5 tail coefficients 45–49
-- statement:
--   For translated local polynomial degrees $45\le n\le49$, the normalized exact translation coefficient has absolute value at most $10^{-32}$. This is an arithmetic tail certificate for the candidate moment polynomial.
-- source:
--   Exact translation of candidate Mellin moment data for the height-124.5 xi polynomial. The earlier theta-jet and Mellin framework is due to sometik179 and Gabewhigham; the additional rounded data and translation certificates are new.

import Definitions.Def_TaoFivePrimes_RH320TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RH124p5RoundedCoefficients14

theorem TaoFivePrimes.rh124p5_translation_tail_group1 : ∀ n : Fin 5,
    (10^32:ℤ)*|RH320TranslationArithmetic.numerator 249 (10^40) (45+n.val)| ≤
      (RH320TranslationArithmetic.denominator:ℤ) := by sorry
