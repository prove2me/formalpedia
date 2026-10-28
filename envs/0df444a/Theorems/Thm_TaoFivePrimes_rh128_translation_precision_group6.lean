-- Prove2me | Theorems.Thm_TaoFivePrimes_rh128_translation_precision_group6
-- name    : TaoFivePrimes.rh128_translation_precision_group6
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:10:31.591492+00:00
-- url     : https://prove2.me/theorems/75552d47-48b1-41fa-91aa-48cb744b7281
-- title:
--   Height-128 precision coefficients 30–34
-- statement:
--   For translated local polynomial degrees $30\le n\le34$, let $a_n$ be the exact coefficient at height $128$ and normalization $10^{41}$, and let $C_n/10^{14}$ be the stored candidate. The absolute error is at most $10^{-14}$ for $n<22$, $2\cdot10^{-15}$ for $22\le n<25$, $10^{-18}$ for $25\le n<30$, and $10^{-24}$ for $30\le n<40$. The exact coefficient is represented by the published integer translation data.
-- source:
--   Exact translation of candidate Mellin moment data for the height-128 xi polynomial. The earlier theta-jet and Mellin framework is due to sometik179 and Gabewhigham; the additional rounded data and translation certificates are new.

import Definitions.Def_TaoFivePrimes_RH336TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RH128RoundedCoefficients14

theorem TaoFivePrimes.rh128_translation_precision_group6 : ∀ n : Fin 5,
    let k := 30+n.val
    (if k<22 then (1:ℤ) else if k<25 then 5 else if k<30 then 10^4 else 10^10) *
      |(10^14:ℤ)*RH336TranslationArithmetic.numerator 256 (10^41) k-
        TaoFivePrimes_RH128RoundedCoefficients14.getD k 0*(RH336TranslationArithmetic.denominator:ℤ)| ≤
          (RH336TranslationArithmetic.denominator:ℤ) := by sorry
