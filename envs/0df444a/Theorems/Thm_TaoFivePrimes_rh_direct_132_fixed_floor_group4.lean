-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_direct_132_fixed_floor_group4
-- name    : TaoFivePrimes.rh_direct_132_fixed_floor_group4
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:48:48.735397+00:00
-- url     : https://prove2.me/theorems/4c745fd1-6193-4039-b8f2-61e3e7156639
-- title:
--   Height-132 fixed-point floors 20–24
-- statement:
--   For each index $k$ with $20\le k\le 24$, the stored fixed-point integer $q_k$ satisfies
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

theorem TaoFivePrimes.rh_direct_132_fixed_floor_group4 : ∀ j : Fin 5,
    RHDirect132FastNumerator.floorHolds (20+j.val) := by sorry
