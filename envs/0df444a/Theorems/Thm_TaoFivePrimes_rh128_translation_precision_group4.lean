-- Prove2me | Theorems.Thm_TaoFivePrimes_rh128_translation_precision_group4
-- name    : TaoFivePrimes.rh128_translation_precision_group4
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:10:26.56785+00:00
-- url     : https://prove2.me/theorems/0a57b704-2245-4078-b3f2-a947c7591940
-- title:
--   Height-128 precision coefficients 20–24
-- statement:
--   For translated local polynomial degrees $20\le n\le24$, let $a_n$ be the exact coefficient at height $128$ and normalization $10^{41}$, and let $C_n/10^{14}$ be the stored candidate. The absolute error is at most $10^{-14}$ for $n<22$, $2\cdot10^{-15}$ for $22\le n<25$, $10^{-18}$ for $25\le n<30$, and $10^{-24}$ for $30\le n<40$. The exact coefficient is represented by the published integer translation data.
-- source:
--   Exact translation of candidate Mellin moment data for the height-128 xi polynomial. The earlier theta-jet and Mellin framework is due to sometik179 and Gabewhigham; the additional rounded data and translation certificates are new.

import Definitions.Def_TaoFivePrimes_RH336TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RH128RoundedCoefficients14

theorem TaoFivePrimes.rh128_translation_precision_group4 : ∀ n : Fin 5,
    let k := 20+n.val
    (if k<22 then (1:ℤ) else if k<25 then 5 else if k<30 then 10^4 else 10^10) *
      |(10^14:ℤ)*RH336TranslationArithmetic.numerator 256 (10^41) k-
        TaoFivePrimes_RH128RoundedCoefficients14.getD k 0*(RH336TranslationArithmetic.denominator:ℤ)| ≤
          (RH336TranslationArithmetic.denominator:ℤ) := by sorry
