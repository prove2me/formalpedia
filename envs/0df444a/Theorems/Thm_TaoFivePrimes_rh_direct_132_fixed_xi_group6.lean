-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_direct_132_fixed_xi_group6
-- name    : TaoFivePrimes.rh_direct_132_fixed_xi_group6
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:52:52.664714+00:00
-- url     : https://prove2.me/theorems/169ec3a1-039e-4567-bbdd-a995f8d5d6b6
-- title:
--   Fixed-point xi rounding arithmetic 30–34
-- statement:
--   For each index $30\le n\le 34$, the complex fixed-point xi candidate equals its parity-based rational expression. The rational candidate also lies within the stored rounding tolerance, with an additional margin of $10^{-43}$. This is a finite exact arithmetic result and does not assert a zero-location theorem.
-- source:
--   Exact arithmetic built on the theta/Mellin and finite quadrature framework of Gabewhigham and sometik179.

import Definitions.Def_TaoFivePrimes_RHDirect132FixedXi
import Mathlib

theorem TaoFivePrimes.rh_direct_132_fixed_xi_group6 : ∀ j : Fin 5,
    RHDirect132FixedXi.xiC (30+j.val) = (RHDirect132FixedXi.xiQ (30+j.val):ℂ) ∧
      RHDirect132FixedXi.roundingHolds (30+j.val) := by sorry
