-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_direct_132_fixed_xi_group4
-- name    : TaoFivePrimes.rh_direct_132_fixed_xi_group4
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:53:11.218315+00:00
-- url     : https://prove2.me/theorems/dce42b89-19d8-497b-ace6-b17cb1e6bde7
-- title:
--   Fixed-point xi rounding arithmetic 20–24
-- statement:
--   For each index $20\le n\le 24$, the complex fixed-point xi candidate equals its parity-based rational expression. The rational candidate also lies within the stored rounding tolerance, with an additional margin of $10^{-43}$. This is a finite exact arithmetic result and does not assert a zero-location theorem.
-- source:
--   Exact arithmetic built on the theta/Mellin and finite quadrature framework of Gabewhigham and sometik179.

import Definitions.Def_TaoFivePrimes_RHDirect132FixedXi
import Mathlib

theorem TaoFivePrimes.rh_direct_132_fixed_xi_group4 : ∀ j : Fin 5,
    RHDirect132FixedXi.xiC (20+j.val) = (RHDirect132FixedXi.xiQ (20+j.val):ℂ) ∧
      RHDirect132FixedXi.roundingHolds (20+j.val) := by sorry
