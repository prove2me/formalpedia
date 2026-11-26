-- Prove2me | Theorems.Thm_RHHeight1000_em_t48711_head24_enclosure
-- name    : RHHeight1000.em_t48711_head24_enclosure
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-19T08:21:49.415554+00:00
-- url     : https://prove2.me/theorems/db719ae9-cc76-41c8-ac52-586911fa943a
-- title:
--   Exact enclosure of the first 24 Dirichlet terms at one half plus 48.711 i
-- statement:
--   For s = 1/2 + 48.711 i, the sum z of n^(-s) over 1 <= n <= 24 has real and imaginary parts enclosed by the exact rational inequalities in the formal statement. This is a finite-sum certificate used in the Euler–Maclaurin computation; it does not alone prove T1000.
-- source:
--   Salvatore Mercuri and Bhavik Mehta, smmercuri/zeta, commit 3dab6480a82f1bfc5de0a59550e279cf50490033, Apache-2.0. Ordinary kernel-term export of T1000Export.d1198 from the full AXLE T1000 certificate.

import Mathlib
open scoped BigOperators

theorem RHHeight1000.em_t48711_head24_enclosure : let z : ℂ := ∑ n ∈ Finset.Ico (1 : ℕ) 25,
      (n : ℂ) ^ (-((1 : ℂ) / 2 + Complex.I * (((48711 : ℝ) / 1000 : ℝ) : ℂ)))
  |z.re - (39429631493 : ℝ) / 68719476736| ≤ (128710925751 : ℝ) / 68719476736000 ∧
  |z.im - (20347977125 : ℝ) / 549755813888| ≤ (128436149751 : ℝ) / 68719476736000 := by sorry
