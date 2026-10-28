-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_moments_320_enclosed_tight
-- name    : TaoFivePrimes.rh_moments_320_enclosed_tight
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:31:06.32596+00:00
-- url     : https://prove2.me/theorems/604a3b5b-4d81-43c0-861d-b1218960d37f
-- title:
--   Certified scaled Mellin moments through index 319
-- statement:
--   Let $M_j$ be the scaled even Mellin moment of the Riemann-zeta theta kernel and $\widetilde M_j$ the stored candidate. For every integer $0\le j<320$,
--
--   $$
--   |M_j-\widetilde M_j|\le17\cdot10^{-50}.
--   $$
--
--   The enclosure supports a longer global Taylor approximation; it does not itself locate zeros.
-- source:
--   Derived from the proved all-index Mellin rule and cached integer identity. The theta-jet and Mellin framework is due to sometik179, Prove2Me submission c9908072-d99a-4431-aad8-a72c6352619a, https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; theta/Mellin foundations are due to Gabewhigham. The higher moment numerators are new.

import Definitions.Def_TaoFivePrimes_RHMoments320

theorem TaoFivePrimes.rh_moments_320_enclosed_tight (j : ℕ) (hj : j<320) :
    |CertifiedGlobalMoments.moment j-TaoFivePrimes_RHMoments320 j| ≤ 17/10^50 := by sorry
