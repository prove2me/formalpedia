-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_moment_292_293_rounding
-- name    : TaoFivePrimes.rh_moment_292_293_rounding
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:58:06.860187+00:00
-- url     : https://prove2.me/theorems/f68bdefc-9cc0-4534-93a4-ecb10156f74d
-- title:
--   Exact cached Mellin rounding for moments 292–293
-- statement:
--   For each index $292\le j\le293$, let $C_j$ be the stored integer and let $\widetilde Q_j$ be the cached rational Mellin quadrature rule. Then
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

theorem TaoFivePrimes.rh_moment_292_293_rounding : ∀ n : Fin 2,
    let j := 272+20+n.val
    let c := TaoFivePrimes_RHExtendedMomentData272to303.getD (20+n.val) 0
    c*(RHNextMomentInteger.denominator j:ℤ) ≤ 3*(10^64:ℤ)*RHNextMomentCached.numerator j ∧
    3*(10^64:ℤ)*RHNextMomentCached.numerator j < (c+1)*(RHNextMomentInteger.denominator j:ℤ) := by sorry
