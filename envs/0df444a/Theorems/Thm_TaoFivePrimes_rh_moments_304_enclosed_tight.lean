-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_moments_304_enclosed_tight
-- name    : TaoFivePrimes.rh_moments_304_enclosed_tight
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:01:42.9901+00:00
-- url     : https://prove2.me/theorems/d01aefda-7654-4cdb-9efd-fe8cbbf394e2
-- title:
--   Tighter certified Mellin moments through index 303
-- statement:
--   Let $M_j$ be the scaled even Mellin moment and let $\widetilde M_j$ be the published combined rational candidate. For every integer $0\le j<304$,
--
--   $$
--   |M_j-\widetilde M_j|\le17\cdot10^{-50}.
--   $$
--
--   This strengthens the earlier error bound for the same stored moments.
-- source:
--   The original theta/Mellin framework is due to Gabewhigham and sometik179; see https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a. The higher-index rational values and cached integer certificates are recorded in the associated moment-rounding theorems.

import Definitions.Def_TaoFivePrimes_RHMoments304

theorem TaoFivePrimes.rh_moments_304_enclosed_tight (j : ℕ) (hj : j<304) :
    |CertifiedGlobalMoments.moment j-TaoFivePrimes_RHMoments304 j| ≤ 17/10^50 := by sorry
