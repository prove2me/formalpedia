-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_moment_284_285_rounding
-- name    : TaoFivePrimes.rh_moment_284_285_rounding
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T20:00:09.229412+00:00
-- url     : https://prove2.me/theorems/3f385a9b-ab27-4b08-baeb-83163f5531e2
-- title:
--   Exact cached Mellin rounding for moments 284–285
-- statement:
--   For each index $284\le j\le285$, let $C_j$ be the stored integer and let $\widetilde Q_j$ be the cached rational Mellin quadrature rule. Then
--
--   $$
--   C_j\le10^{64}\widetilde Q_j<C_j+1.
--   $$
--
--   The exact rounding certificate supports a true moment enclosure through separately proved rule identities and error bounds.
-- source:
--   Exact cached integer quadrature based on the theta-jet and Mellin framework of sometik179, https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; theta/Mellin foundations by Gabewhigham. The higher rounded values are new.

import Definitions.Def_TaoFivePrimes_RHExtendedMomentData272to303
import Definitions.Def_TaoFivePrimes_RHExtendedMomentCachedNumerator

theorem TaoFivePrimes.rh_moment_284_285_rounding : ∀ n : Fin 2,
    let j := 272+12+n.val
    let c := TaoFivePrimes_RHExtendedMomentData272to303.getD (12+n.val) 0
    c*(RHNextMomentInteger.denominator j:ℤ) ≤ 3*(10^64:ℤ)*RHNextMomentCached.numerator j ∧
    3*(10^64:ℤ)*RHNextMomentCached.numerator j < (c+1)*(RHNextMomentInteger.denominator j:ℤ) := by sorry
