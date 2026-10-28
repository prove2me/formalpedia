-- Prove2me | Theorems.Thm_TaoFivePrimes_rh123_translation_precision_group2
-- name    : TaoFivePrimes.rh123_translation_precision_group2
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:35:42.176169+00:00
-- url     : https://prove2.me/theorems/d246b818-b3f7-4b31-a709-821b586e1ddb
-- title:
--   Height-123 precision coefficients 10–14
-- statement:
--   For translated local polynomial degrees $10\le n\le14$, let $a_n$ be the exact coefficient at height $123$ and normalization $10^{40}$, and let $C_n/10^{12}$ be the stored candidate. The absolute error is at most $10^{-12}$ for $n<20$, $10^{-13}$ for $20\le n<25$, $10^{-16}$ for $25\le n<30$, and $10^{-20}$ for $30\le n<40$. The exact coefficient is represented by the published integer translation data.
-- source:
--   Exact translation of candidate Mellin moment data for the height-123 xi polynomial. The earlier theta-jet and Mellin framework is due to sometik179 and Gabewhigham; the additional rounded data and translation certificates are new.

import Definitions.Def_TaoFivePrimes_RH320TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RH123RoundedCoefficients12

theorem TaoFivePrimes.rh123_translation_precision_group2 : ∀ n : Fin 5,
    let k := 10+n.val
    (if k<20 then (1:ℤ) else if k<25 then 10 else if k<30 then 10^4 else 10^8) *
      |(10^12:ℤ)*RH320TranslationArithmetic.numerator 246 (10^40) k-
        TaoFivePrimes_RH123RoundedCoefficients12.getD k 0*(RH320TranslationArithmetic.denominator:ℤ)| ≤
          (RH320TranslationArithmetic.denominator:ℤ) := by sorry
