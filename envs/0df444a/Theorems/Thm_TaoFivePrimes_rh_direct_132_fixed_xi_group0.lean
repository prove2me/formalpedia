-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_direct_132_fixed_xi_group0
-- name    : TaoFivePrimes.rh_direct_132_fixed_xi_group0
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:52:56.106349+00:00
-- url     : https://prove2.me/theorems/5ca523bb-5c7f-4d9e-9dde-da02f7b9980d
-- title:
--   Fixed-point xi rounding arithmetic 0–4
-- statement:
--   For each index $0\le n\le 4$, the complex fixed-point xi candidate equals its parity-based rational expression. The rational candidate also lies within the stored rounding tolerance, with an additional margin of $10^{-43}$. This is a finite exact arithmetic result and does not assert a zero-location theorem.
-- source:
--   Exact arithmetic built on the theta/Mellin and finite quadrature framework of Gabewhigham and sometik179.

import Definitions.Def_TaoFivePrimes_RHDirect132FixedXi
import Mathlib

theorem TaoFivePrimes.rh_direct_132_fixed_xi_group0 : ∀ j : Fin 5,
    RHDirect132FixedXi.xiC (0+j.val) = (RHDirect132FixedXi.xiQ (0+j.val):ℂ) ∧
      RHDirect132FixedXi.roundingHolds (0+j.val) := by sorry
