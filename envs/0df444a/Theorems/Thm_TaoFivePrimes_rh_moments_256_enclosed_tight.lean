-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_moments_256_enclosed_tight
-- name    : TaoFivePrimes.rh_moments_256_enclosed_tight
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T20:59:44.517476+00:00
-- url     : https://prove2.me/theorems/95fbb242-ebc4-4483-ad05-17a0f60b595d
-- title:
--   Tighter certified Mellin moments through index 255
-- statement:
--   Let $M_j$ be the scaled even Mellin moment and let $\widetilde M_j$ be the existing stored rational candidate. For every integer $0\le j<256$,
--
--   $$
--   |M_j-\widetilde M_j|\le17\cdot10^{-50}.
--   $$
--
--   This improves the previously published $10^{-46}$ error bound for those same candidates.
-- source:
--   The numerical data and packed certificate are due to sometik179, https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; theta/Mellin foundations are due to Gabewhigham. The accepted original 256-moment enclosure is https://prove2.me/submissions/eeacb653-f10b-4f9a-941c-c976113b9f30.

import Definitions.Def_TaoFivePrimes_RH14To100MomentModel

theorem TaoFivePrimes.rh_moments_256_enclosed_tight (j : ℕ) (hj : j<256) :
    |CertifiedGlobalMoments.moment j-CertifiedGlobalMomentEnclosure.candidateMoment j|≤ 17/10^50 := by sorry
