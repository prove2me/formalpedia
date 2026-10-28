-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_moments_336_enclosed_1e55
-- name    : TaoFivePrimes.rh_moments_336_enclosed_1e55
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:06:29.577582+00:00
-- url     : https://prove2.me/theorems/ce6657d5-4ac2-4ee6-af41-6ea72c9866e1
-- title:
--   Improved certified Mellin moments through index 335
-- statement:
--   Let $M_j$ be the scaled even Mellin moment and $\widetilde M_j$ the stored rational candidate. For every integer $0\le j<336$,
--
--   $$
--   |M_j-\widetilde M_j|\le162\cdot10^{-57}.
--   $$
--
--   The enclosure supports a longer global Taylor approximation; it does not itself locate zeros.
-- source:
--   The theta-jet and Mellin framework is due to sometik179, https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; theta/Mellin foundations are due to Gabewhigham. The wider Cauchy-circle estimate is a separate dependency.

import Definitions.Def_TaoFivePrimes_RHMoments336

theorem TaoFivePrimes.rh_moments_336_enclosed_1e55 (j : ℕ) (hj : j<336) :
    |CertifiedGlobalMoments.moment j-TaoFivePrimes_RHMoments336 j| ≤ 162/10^57 := by sorry
