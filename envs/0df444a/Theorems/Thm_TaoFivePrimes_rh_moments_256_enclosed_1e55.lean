-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_moments_256_enclosed_1e55
-- name    : TaoFivePrimes.rh_moments_256_enclosed_1e55
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:04:13.235769+00:00
-- url     : https://prove2.me/theorems/8e1a78bf-a5c6-46d8-91e5-3dc7b63f67ce
-- title:
--   Improved certified Mellin moments through index 255
-- statement:
--   Let $M_j$ be the scaled even Mellin moment and $\widetilde M_j$ the stored rational candidate. For every integer $0\le j<256$,
--
--   $$
--   |M_j-\widetilde M_j|\le162\cdot10^{-57}.
--   $$
--
--   The same stored moment data therefore admit a sharper enclosure.
-- source:
--   The theta-jet and Mellin framework is due to sometik179, https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; theta/Mellin foundations are due to Gabewhigham. The wider Cauchy-circle estimate is a separate dependency.

import Definitions.Def_TaoFivePrimes_RH14To100MomentModel

theorem TaoFivePrimes.rh_moments_256_enclosed_1e55 (j : ℕ) (hj : j<256) :
    |CertifiedGlobalMoments.moment j-CertifiedGlobalMomentEnclosure.candidateMoment j|≤ 162/10^57 := by sorry
