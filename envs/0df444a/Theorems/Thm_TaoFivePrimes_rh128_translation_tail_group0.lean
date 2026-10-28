-- Prove2me | Theorems.Thm_TaoFivePrimes_rh128_translation_tail_group0
-- name    : TaoFivePrimes.rh128_translation_tail_group0
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:10:22.877374+00:00
-- url     : https://prove2.me/theorems/6277a18b-e345-4102-907b-f5555eeb119e
-- title:
--   Height-128 tail coefficients 40–44
-- statement:
--   For translated local polynomial degrees $40\le n\le44$, the normalized exact translation coefficient has absolute value at most $10^{-32}$. This is an arithmetic tail certificate for the candidate moment polynomial.
-- source:
--   Exact translation of candidate Mellin moment data for the height-128 xi polynomial. The earlier theta-jet and Mellin framework is due to sometik179 and Gabewhigham; the additional rounded data and translation certificates are new.

import Definitions.Def_TaoFivePrimes_RH336TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RH128RoundedCoefficients14

theorem TaoFivePrimes.rh128_translation_tail_group0 : ∀ n : Fin 5,
    (10^32:ℤ)*|RH336TranslationArithmetic.numerator 256 (10^41) (40+n.val)| ≤
      (RH336TranslationArithmetic.denominator:ℤ) := by sorry
