-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_moments_272_enclosed
-- name    : TaoFivePrimes.rh_moments_272_enclosed
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:15:26.424202+00:00
-- url     : https://prove2.me/theorems/9b02668e-1188-4d32-88cd-4edb1e5c776d
-- title:
--   Certified scaled Mellin moments through index 271
-- statement:
--   Let $M_j$ be the scaled even Mellin moment of the Riemann-zeta theta kernel and let $\widetilde M_j$ be the combined candidate list. For every integer $0\le j<272$,
--
--   $$
--   |M_j-\widetilde M_j|\le2\cdot10^{-46}.
--   $$
--
--   The first 256 entries come from the earlier moment certificate; the last sixteen extend the data available for Taylor approximations. The moment enclosure alone asserts no zeta zero-location statement.
-- source:
--   The first 256 moment data and analytic/theta-jet framework are due to sometik179, Prove2Me c9908072-d99a-4431-aad8-a72c6352619a, https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; theta/Mellin foundations by Gabewhigham. The 16 additional rounded moments are derived here from the general rational-rule enclosure and exact integer certificates.

import Definitions.Def_TaoFivePrimes_RHMoments272

theorem TaoFivePrimes.rh_moments_272_enclosed (j : ℕ) (hj : j<272) :
    |CertifiedGlobalMoments.moment j-TaoFivePrimes_RHMoments272 j| ≤ 2/10^46 := by sorry
