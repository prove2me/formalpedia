-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_moments_272_enclosed_tight
-- name    : TaoFivePrimes.rh_moments_272_enclosed_tight
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:01:41.844986+00:00
-- url     : https://prove2.me/theorems/488864d7-c6ec-4d20-a7fc-0e4593af8efd
-- title:
--   Tighter certified Mellin moments through index 271
-- statement:
--   Let $M_j$ be the scaled even Mellin moment and let $\widetilde M_j$ be the published combined rational candidate. For every integer $0\le j<272$,
--
--   $$
--   |M_j-\widetilde M_j|\le17\cdot10^{-50}.
--   $$
--
--   This strengthens the earlier error bound for the same stored moments.
-- source:
--   The original theta/Mellin framework is due to Gabewhigham and sometik179; see https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a. The higher-index rational values and cached integer certificates are recorded in the associated moment-rounding theorems.

import Definitions.Def_TaoFivePrimes_RHMoments272

theorem TaoFivePrimes.rh_moments_272_enclosed_tight (j : ℕ) (hj : j<272) :
    |CertifiedGlobalMoments.moment j-TaoFivePrimes_RHMoments272 j| ≤ 17/10^50 := by sorry
