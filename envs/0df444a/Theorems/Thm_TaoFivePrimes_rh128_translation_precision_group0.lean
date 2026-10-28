-- Prove2me | Theorems.Thm_TaoFivePrimes_rh128_translation_precision_group0
-- name    : TaoFivePrimes.rh128_translation_precision_group0
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:10:28.355994+00:00
-- url     : https://prove2.me/theorems/46ce5d8f-5727-40bf-9ee7-3b27bb802e25
-- title:
--   Height-128 precision coefficients 0–4
-- statement:
--   For translated local polynomial degrees $0\le n\le4$, let $a_n$ be the exact coefficient at height $128$ and normalization $10^{41}$, and let $C_n/10^{14}$ be the stored candidate. The absolute error is at most $10^{-14}$ for $n<22$, $2\cdot10^{-15}$ for $22\le n<25$, $10^{-18}$ for $25\le n<30$, and $10^{-24}$ for $30\le n<40$. The exact coefficient is represented by the published integer translation data.
-- source:
--   Exact translation of candidate Mellin moment data for the height-128 xi polynomial. The earlier theta-jet and Mellin framework is due to sometik179 and Gabewhigham; the additional rounded data and translation certificates are new.

import Definitions.Def_TaoFivePrimes_RH336TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RH128RoundedCoefficients14

theorem TaoFivePrimes.rh128_translation_precision_group0 : ∀ n : Fin 5,
    let k := 0+n.val
    (if k<22 then (1:ℤ) else if k<25 then 5 else if k<30 then 10^4 else 10^10) *
      |(10^14:ℤ)*RH336TranslationArithmetic.numerator 256 (10^41) k-
        TaoFivePrimes_RH128RoundedCoefficients14.getD k 0*(RH336TranslationArithmetic.denominator:ℤ)| ≤
          (RH336TranslationArithmetic.denominator:ℤ) := by sorry
