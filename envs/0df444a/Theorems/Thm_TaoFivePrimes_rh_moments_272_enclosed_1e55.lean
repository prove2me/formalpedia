-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_moments_272_enclosed_1e55
-- name    : TaoFivePrimes.rh_moments_272_enclosed_1e55
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:05:45.626552+00:00
-- url     : https://prove2.me/theorems/9daefe7f-9fe2-4a5b-a885-6b7801f73eed
-- title:
--   Improved certified Mellin moments through index 271
-- statement:
--   Let $M_j$ be the scaled even Mellin moment and $\widetilde M_j$ the stored rational candidate. For every integer $0\le j<272$,
--
--   $$
--   |M_j-\widetilde M_j|\le162\cdot10^{-57}.
--   $$
--
--   The enclosure supports a longer global Taylor approximation; it does not itself locate zeros.
-- source:
--   The theta-jet and Mellin framework is due to sometik179, https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; theta/Mellin foundations are due to Gabewhigham. The wider Cauchy-circle estimate is a separate dependency.

import Definitions.Def_TaoFivePrimes_RHMoments272

theorem TaoFivePrimes.rh_moments_272_enclosed_1e55 (j : ℕ) (hj : j<272) :
    |CertifiedGlobalMoments.moment j-TaoFivePrimes_RHMoments272 j| ≤ 162/10^57 := by sorry
