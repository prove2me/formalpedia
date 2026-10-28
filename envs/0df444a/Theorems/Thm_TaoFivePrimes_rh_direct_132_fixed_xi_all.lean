-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_direct_132_fixed_xi_all
-- name    : TaoFivePrimes.rh_direct_132_fixed_xi_all
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:56:15.713335+00:00
-- url     : https://prove2.me/theorems/d1edff42-6802-4463-adcb-b994f87581d8
-- title:
--   Fixed-point xi arithmetic through index 59
-- statement:
--   For every integer $0\le n<60$, the complex fixed-point xi candidate equals its parity-based rational expression. The rational candidate lies within the stored coefficient tolerance with an additional margin of $10^{-43}$. This combines twelve exact finite-arithmetic certificates.
-- source:
--   Exact finite arithmetic based on the theta/Mellin framework of Gabewhigham and sometik179.

import Definitions.Def_TaoFivePrimes_RHDirect132FixedXi
import Mathlib

theorem TaoFivePrimes.rh_direct_132_fixed_xi_all (n : ℕ) (hn : n<60) : RHDirect132FixedXi.xiC n = (RHDirect132FixedXi.xiQ n:ℂ) ∧ RHDirect132FixedXi.roundingHolds n := by sorry
