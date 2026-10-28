-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_direct_132_fixed_xi_group1
-- name    : TaoFivePrimes.rh_direct_132_fixed_xi_group1
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:53:08.893729+00:00
-- url     : https://prove2.me/theorems/f214aaa5-a19d-48fe-8fb0-65741199a197
-- title:
--   Fixed-point xi rounding arithmetic 5–9
-- statement:
--   For each index $5\le n\le 9$, the complex fixed-point xi candidate equals its parity-based rational expression. The rational candidate also lies within the stored rounding tolerance, with an additional margin of $10^{-43}$. This is a finite exact arithmetic result and does not assert a zero-location theorem.
-- source:
--   Exact arithmetic built on the theta/Mellin and finite quadrature framework of Gabewhigham and sometik179.

import Definitions.Def_TaoFivePrimes_RHDirect132FixedXi
import Mathlib

theorem TaoFivePrimes.rh_direct_132_fixed_xi_group1 : ∀ j : Fin 5,
    RHDirect132FixedXi.xiC (5+j.val) = (RHDirect132FixedXi.xiQ (5+j.val):ℂ) ∧
      RHDirect132FixedXi.roundingHolds (5+j.val) := by sorry
