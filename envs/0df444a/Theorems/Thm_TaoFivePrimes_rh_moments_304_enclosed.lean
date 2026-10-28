-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_moments_304_enclosed
-- name    : TaoFivePrimes.rh_moments_304_enclosed
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:49:08.159758+00:00
-- url     : https://prove2.me/theorems/ebd352d3-e89f-4bbd-9cd4-b602400e36d9
-- title:
--   Certified scaled Mellin moments through index 303
-- statement:
--   Let $M_j$ denote the scaled even Mellin moment of the Riemann-zeta theta kernel and let $\widetilde M_j$ be the combined candidate value. For every integer $0\le j<304$,
--
--   $$
--   |M_j-\widetilde M_j|\le2\cdot10^{-46}.
--   $$
--
--   This extends the earlier 272-moment enclosure with 32 further values, supporting longer global Taylor approximations. It is not by itself a zero-location statement.
-- source:
--   Derived from the proved all-index Mellin rule and cached integer identity. The theta-jet and Mellin framework is due to sometik179, Prove2Me submission c9908072-d99a-4431-aad8-a72c6352619a, https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; theta/Mellin foundations are due to Gabewhigham. The higher moment numerators are new.

import Definitions.Def_TaoFivePrimes_RHMoments304

theorem TaoFivePrimes.rh_moments_304_enclosed (j : ℕ) (hj : j<304) :
    |CertifiedGlobalMoments.moment j-TaoFivePrimes_RHMoments304 j| ≤ 2/10^46 := by sorry
