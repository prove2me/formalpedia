-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_direct_132_fixed_xi_group3
-- name    : TaoFivePrimes.rh_direct_132_fixed_xi_group3
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:52:59.783032+00:00
-- url     : https://prove2.me/theorems/c14c5ce2-dbb3-43aa-8a4d-58f2111cf282
-- title:
--   Fixed-point xi rounding arithmetic 15–19
-- statement:
--   For each index $15\le n\le 19$, the complex fixed-point xi candidate equals its parity-based rational expression. The rational candidate also lies within the stored rounding tolerance, with an additional margin of $10^{-43}$. This is a finite exact arithmetic result and does not assert a zero-location theorem.
-- source:
--   Exact arithmetic built on the theta/Mellin and finite quadrature framework of Gabewhigham and sometik179.

import Definitions.Def_TaoFivePrimes_RHDirect132FixedXi
import Mathlib

theorem TaoFivePrimes.rh_direct_132_fixed_xi_group3 : ∀ j : Fin 5,
    RHDirect132FixedXi.xiC (15+j.val) = (RHDirect132FixedXi.xiQ (15+j.val):ℂ) ∧
      RHDirect132FixedXi.roundingHolds (15+j.val) := by sorry
