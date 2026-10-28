-- Prove2me | Theorems.Thm_TaoFivePrimes_rh123_translation_precision_group0
-- name    : TaoFivePrimes.rh123_translation_precision_group0
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:35:38.207121+00:00
-- url     : https://prove2.me/theorems/e69aa6b0-8227-4c50-96e0-294a86efdd12
-- title:
--   Height-123 precision coefficients 0–4
-- statement:
--   For translated local polynomial degrees $0\le n\le4$, let $a_n$ be the exact coefficient at height $123$ and normalization $10^{40}$, and let $C_n/10^{12}$ be the stored candidate. The absolute error is at most $10^{-12}$ for $n<20$, $10^{-13}$ for $20\le n<25$, $10^{-16}$ for $25\le n<30$, and $10^{-20}$ for $30\le n<40$. The exact coefficient is represented by the published integer translation data.
-- source:
--   Exact translation of candidate Mellin moment data for the height-123 xi polynomial. The earlier theta-jet and Mellin framework is due to sometik179 and Gabewhigham; the additional rounded data and translation certificates are new.

import Definitions.Def_TaoFivePrimes_RH320TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RH123RoundedCoefficients12

theorem TaoFivePrimes.rh123_translation_precision_group0 : ∀ n : Fin 5,
    let k := 0+n.val
    (if k<20 then (1:ℤ) else if k<25 then 10 else if k<30 then 10^4 else 10^8) *
      |(10^12:ℤ)*RH320TranslationArithmetic.numerator 246 (10^40) k-
        TaoFivePrimes_RH123RoundedCoefficients12.getD k 0*(RH320TranslationArithmetic.denominator:ℤ)| ≤
          (RH320TranslationArithmetic.denominator:ℤ) := by sorry
