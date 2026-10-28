-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_moment_304_305_rounding
-- name    : TaoFivePrimes.rh_moment_304_305_rounding
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:30:07.534248+00:00
-- url     : https://prove2.me/theorems/c7aca183-72ec-458d-a1d9-f5b7e0c0cad4
-- title:
--   Rounded cached Mellin values for moments 304–305
-- statement:
--   For $j=304,305$, let $C_j$ be the stored integer and let $\widetilde Q_j=3\widetilde N_j/D_j$ be the cached rational Mellin quadrature rule. Then
--
--   $$
--   C_j\le10^{64}\widetilde Q_j<C_j+1.
--   $$
--
--   This exact integer rounding certificate concerns the rational rule; the enclosure of the true moment is separate.
-- source:
--   Derived from the proved all-index Mellin rule and cached integer identity. The theta-jet and Mellin framework is due to sometik179, Prove2Me submission c9908072-d99a-4431-aad8-a72c6352619a, https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; theta/Mellin foundations are due to Gabewhigham. The higher moment numerators are new.

import Definitions.Def_TaoFivePrimes_RHExtendedMomentData304to319
import Definitions.Def_TaoFivePrimes_RHExtendedMomentCachedNumerator

theorem TaoFivePrimes.rh_moment_304_305_rounding : ∀ n : Fin 2,
    let j := 304+0+n.val
    let c := TaoFivePrimes_RHExtendedMomentData304to319.getD (0+n.val) 0
    c*(RHNextMomentInteger.denominator j:ℤ) ≤ 3*(10^64:ℤ)*RHNextMomentCached.numerator j ∧
    3*(10^64:ℤ)*RHNextMomentCached.numerator j < (c+1)*(RHNextMomentInteger.denominator j:ℤ) := by sorry
