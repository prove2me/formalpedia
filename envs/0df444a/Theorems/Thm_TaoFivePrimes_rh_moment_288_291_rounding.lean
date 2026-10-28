-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_moment_288_291_rounding
-- name    : TaoFivePrimes.rh_moment_288_291_rounding
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:47:37.622125+00:00
-- url     : https://prove2.me/theorems/6037dd67-a227-4a9f-84ff-15dc568473fa
-- title:
--   Exact rounded cached Mellin values for moments 288–291
-- statement:
--   For each index $288\le j\le291$, let $C_j$ be the stored integer and let $\widetilde Q_j=3\widetilde N_j/D_j$ denote the cached rational Mellin quadrature rule. Then
--
--   $$
--   C_j\le10^{64}\widetilde Q_j<C_j+1.
--   $$
--
--   This is an exact integer rounding certificate for the rational rule; an enclosure for the true moment is proved separately.
-- source:
--   Derived from the proved all-index Mellin rule and cached integer identity. The theta-jet and Mellin framework is due to sometik179, Prove2Me submission c9908072-d99a-4431-aad8-a72c6352619a, https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; theta/Mellin foundations are due to Gabewhigham. The higher moment numerators are new.

import Definitions.Def_TaoFivePrimes_RHExtendedMomentData272to303
import Definitions.Def_TaoFivePrimes_RHExtendedMomentCachedNumerator

theorem TaoFivePrimes.rh_moment_288_291_rounding : ∀ n : Fin 4,
    let j := 272+16+n.val
    let c := TaoFivePrimes_RHExtendedMomentData272to303.getD (16+n.val) 0
    c*(RHNextMomentInteger.denominator j:ℤ) ≤ 3*(10^64:ℤ)*RHNextMomentCached.numerator j ∧
    3*(10^64:ℤ)*RHNextMomentCached.numerator j < (c+1)*(RHNextMomentInteger.denominator j:ℤ) := by sorry
