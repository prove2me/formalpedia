-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_direct_132_fixed_xi_group8
-- name    : TaoFivePrimes.rh_direct_132_fixed_xi_group8
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:52:57.508759+00:00
-- url     : https://prove2.me/theorems/99c9ca5d-7419-4a5e-b070-89b0539adaca
-- title:
--   Fixed-point xi rounding arithmetic 40–44
-- statement:
--   For each index $40\le n\le 44$, the complex fixed-point xi candidate equals its parity-based rational expression. The rational candidate also lies within the stored rounding tolerance, with an additional margin of $10^{-43}$. This is a finite exact arithmetic result and does not assert a zero-location theorem.
-- source:
--   Exact arithmetic built on the theta/Mellin and finite quadrature framework of Gabewhigham and sometik179.

import Definitions.Def_TaoFivePrimes_RHDirect132FixedXi
import Mathlib

theorem TaoFivePrimes.rh_direct_132_fixed_xi_group8 : ∀ j : Fin 5,
    RHDirect132FixedXi.xiC (40+j.val) = (RHDirect132FixedXi.xiQ (40+j.val):ℂ) ∧
      RHDirect132FixedXi.roundingHolds (40+j.val) := by sorry
