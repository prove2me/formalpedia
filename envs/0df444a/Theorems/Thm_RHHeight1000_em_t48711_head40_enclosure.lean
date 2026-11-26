-- Prove2me | Theorems.Thm_RHHeight1000_em_t48711_head40_enclosure
-- name    : RHHeight1000.em_t48711_head40_enclosure
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-19T08:28:16.54736+00:00
-- url     : https://prove2.me/theorems/9b90cfb7-8370-42f8-874d-4d7620898bc1
-- title:
--   Exact enclosure of the first 40 Dirichlet terms at one half plus 48.711 i
-- statement:
--   Set $s=\tfrac12+48.711i$ and $z=\sum_{n=1}^{40}n^{-s}$. Then
--   $$\left|\Re z-\frac{612813288183}{1099511627776}\right|\le\frac{1779186709967}{687194767360000},$$
--   $$\left|\Im z+\frac{50694497679}{1099511627776}\right|\le\frac{1776139299967}{687194767360000}.$$
--   These bounds certify the finite-sum contribution to an Euler–Maclaurin evaluation used in the height-1000 zero computation.
-- source:
--   Salvatore Mercuri and Bhavik Mehta, smmercuri/zeta, commit 3dab6480a82f1bfc5de0a59550e279cf50490033, Apache-2.0. Ordinary kernel-term export of T1000Export.d1200 from the full AXLE T1000 certificate.

import Mathlib
open scoped BigOperators

theorem RHHeight1000.em_t48711_head40_enclosure : let z : ℂ := ∑ n ∈ Finset.Ico (1 : ℕ) 41,
      (n : ℂ) ^ (-((1 : ℂ) / 2 + Complex.I * (((48711 : ℝ) / 1000 : ℝ) : ℂ)))
  |z.re - (612813288183 : ℝ) / 1099511627776| ≤ (1779186709967 : ℝ) / 687194767360000 ∧
  |z.im + (50694497679 : ℝ) / 1099511627776| ≤ (1776139299967 : ℝ) / 687194767360000 := by sorry
