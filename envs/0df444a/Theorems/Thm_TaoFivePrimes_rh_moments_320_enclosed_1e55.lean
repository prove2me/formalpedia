-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_moments_320_enclosed_1e55
-- name    : TaoFivePrimes.rh_moments_320_enclosed_1e55
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:05:44.657157+00:00
-- url     : https://prove2.me/theorems/c1981a09-71bb-47d0-b4eb-9a289117eacb
-- title:
--   Improved certified Mellin moments through index 319
-- statement:
--   Let $M_j$ be the scaled even Mellin moment and $\widetilde M_j$ the stored rational candidate. For every integer $0\le j<320$,
--
--   $$
--   |M_j-\widetilde M_j|\le162\cdot10^{-57}.
--   $$
--
--   The enclosure supports a longer global Taylor approximation; it does not itself locate zeros.
-- source:
--   The theta-jet and Mellin framework is due to sometik179, https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; theta/Mellin foundations are due to Gabewhigham. The wider Cauchy-circle estimate is a separate dependency.

import Definitions.Def_TaoFivePrimes_RHMoments320

theorem TaoFivePrimes.rh_moments_320_enclosed_1e55 (j : ℕ) (hj : j<320) :
    |CertifiedGlobalMoments.moment j-TaoFivePrimes_RHMoments320 j| ≤ 162/10^57 := by sorry
