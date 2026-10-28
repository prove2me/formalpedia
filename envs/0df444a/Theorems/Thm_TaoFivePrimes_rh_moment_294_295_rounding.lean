-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_moment_294_295_rounding
-- name    : TaoFivePrimes.rh_moment_294_295_rounding
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:57:57.10037+00:00
-- url     : https://prove2.me/theorems/4994ffa2-abbb-4016-990a-97bc67196142
-- title:
--   Exact cached Mellin rounding for moments 294–295
-- statement:
--   For each index $294\le j\le295$, let $C_j$ be the stored integer and let $\widetilde Q_j$ be the cached rational Mellin quadrature rule. Then
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

theorem TaoFivePrimes.rh_moment_294_295_rounding : ∀ n : Fin 2,
    let j := 272+22+n.val
    let c := TaoFivePrimes_RHExtendedMomentData272to303.getD (22+n.val) 0
    c*(RHNextMomentInteger.denominator j:ℤ) ≤ 3*(10^64:ℤ)*RHNextMomentCached.numerator j ∧
    3*(10^64:ℤ)*RHNextMomentCached.numerator j < (c+1)*(RHNextMomentInteger.denominator j:ℤ) := by sorry
