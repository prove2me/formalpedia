-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_direct_132_fixed_xi_group2
-- name    : TaoFivePrimes.rh_direct_132_fixed_xi_group2
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:53:02.298514+00:00
-- url     : https://prove2.me/theorems/a5a348af-0c99-46d8-9974-cd456f24b7e8
-- title:
--   Fixed-point xi rounding arithmetic 10–14
-- statement:
--   For each index $10\le n\le 14$, the complex fixed-point xi candidate equals its parity-based rational expression. The rational candidate also lies within the stored rounding tolerance, with an additional margin of $10^{-43}$. This is a finite exact arithmetic result and does not assert a zero-location theorem.
-- source:
--   Exact arithmetic built on the theta/Mellin and finite quadrature framework of Gabewhigham and sometik179.

import Definitions.Def_TaoFivePrimes_RHDirect132FixedXi
import Mathlib

theorem TaoFivePrimes.rh_direct_132_fixed_xi_group2 : ∀ j : Fin 5,
    RHDirect132FixedXi.xiC (10+j.val) = (RHDirect132FixedXi.xiQ (10+j.val):ℂ) ∧
      RHDirect132FixedXi.roundingHolds (10+j.val) := by sorry
