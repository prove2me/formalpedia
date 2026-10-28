-- Prove2me | Theorems.Thm_TaoFivePrimes_rh123_translation_tail_group1
-- name    : TaoFivePrimes.rh123_translation_tail_group1
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:35:43.742225+00:00
-- url     : https://prove2.me/theorems/946ffed3-be2f-4b97-8c97-084dfc99bee3
-- title:
--   Height-123 tail coefficients 45–49
-- statement:
--   For translated local polynomial degrees $45\le n\le49$, the normalized exact translation coefficient has absolute value at most $10^{-32}$. This is an arithmetic tail certificate for the candidate moment polynomial.
-- source:
--   Exact translation of candidate Mellin moment data for the height-123 xi polynomial. The earlier theta-jet and Mellin framework is due to sometik179 and Gabewhigham; the additional rounded data and translation certificates are new.

import Definitions.Def_TaoFivePrimes_RH320TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RH123RoundedCoefficients12

theorem TaoFivePrimes.rh123_translation_tail_group1 : ∀ n : Fin 5,
    (10^32:ℤ)*|RH320TranslationArithmetic.numerator 246 (10^40) (45+n.val)| ≤
      (RH320TranslationArithmetic.denominator:ℤ) := by sorry
