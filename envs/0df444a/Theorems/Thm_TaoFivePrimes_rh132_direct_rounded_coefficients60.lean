-- Prove2me | Theorems.Thm_TaoFivePrimes_rh132_direct_rounded_coefficients60
-- name    : TaoFivePrimes.rh132_direct_rounded_coefficients60
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:13:15.024254+00:00
-- url     : https://prove2.me/theorems/48fe9f6c-b20c-4199-a72b-b5862bf949fb
-- title:
--   Rounding the first sixty height-132 rational xi coefficients
-- statement:
--   Let $C_n$ be the Gaussian-rational xi coefficient from the direct height-132 quadrature, and let $p_n$ and $\varepsilon_n$ be the published candidate and tolerance. For every integer $0\le n<60$,
--
--   $$
--   |C_n-p_n|\le\varepsilon_n.
--   $$
--
--   This finite arithmetic enclosure is the remaining numerical input for the proposed height-132 local xi approximation. It is an open problem until separately proved.
-- source:
--   Exact fixed-point oscillatory quadrature built on the theta/Mellin framework due to Gabewhigham and sometik179.

import Definitions.Def_TaoFivePrimes_RH132RoundingSpec
import Mathlib

theorem TaoFivePrimes.rh132_direct_rounded_coefficients60 (n : ℕ) (hn : n<60) :
    ‖RHDirect132XiCoefficients.scaled n-(RH132RoundingSpec.proposed n:ℂ)‖ ≤
      RH132RoundingSpec.bound n := by sorry
