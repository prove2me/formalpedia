-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_direct_132_fixed_floor_group5
-- name    : TaoFivePrimes.rh_direct_132_fixed_floor_group5
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:48:45.997074+00:00
-- url     : https://prove2.me/theorems/3d359156-592e-4ef4-8221-f4119b3ccb7f
-- title:
--   Height-132 fixed-point floors 25–29
-- statement:
--   For each index $k$ with $25\le k\le 29$, the stored fixed-point integer $q_k$ satisfies
--
--   $$
--   q_kD_k\le10^{90}3^{k+1}N_k<(q_k+1)D_k,
--   $$
--
--   where $N_k$ is the parity-selected factorial-based cached numerator and $D_k$ is the cached positive denominator. This is a finite exact integer certificate.
-- source:
--   Finite theta-jet and Mellin quadrature framework by sometik179 and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHDirect132FastNumerator
import Mathlib

theorem TaoFivePrimes.rh_direct_132_fixed_floor_group5 : ∀ j : Fin 5,
    RHDirect132FastNumerator.floorHolds (25+j.val) := by sorry
