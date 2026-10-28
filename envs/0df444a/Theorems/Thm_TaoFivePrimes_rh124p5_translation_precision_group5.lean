-- Prove2me | Theorems.Thm_TaoFivePrimes_rh124p5_translation_precision_group5
-- name    : TaoFivePrimes.rh124p5_translation_precision_group5
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:46:55.635735+00:00
-- url     : https://prove2.me/theorems/4fb5a8b9-758d-4dda-9450-0133d661d9b1
-- title:
--   Height-124.5 precision coefficients 25–29
-- statement:
--   For translated local polynomial degrees $25\le n\le29$, let $a_n$ be the exact coefficient at height $124.5$ and normalization $10^{40}$, and let $C_n/10^{14}$ be the stored candidate. The absolute error is at most $10^{-14}$ for $n<22$, $10^{-15}$ for $22\le n<25$, $10^{-18}$ for $25\le n<30$, and $10^{-24}$ for $30\le n<40$. The exact coefficient is represented by the published integer translation data.
-- source:
--   Exact translation of candidate Mellin moment data for the height-124.5 xi polynomial. The earlier theta-jet and Mellin framework is due to sometik179 and Gabewhigham; the additional rounded data and translation certificates are new.

import Definitions.Def_TaoFivePrimes_RH320TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RH124p5RoundedCoefficients14

theorem TaoFivePrimes.rh124p5_translation_precision_group5 : ∀ n : Fin 5,
    let k := 25+n.val
    (if k<22 then (1:ℤ) else if k<25 then 10 else if k<30 then 10^4 else 10^10) *
      |(10^14:ℤ)*RH320TranslationArithmetic.numerator 249 (10^40) k-
        TaoFivePrimes_RH124p5RoundedCoefficients14.getD k 0*(RH320TranslationArithmetic.denominator:ℤ)| ≤
          (RH320TranslationArithmetic.denominator:ℤ) := by sorry
