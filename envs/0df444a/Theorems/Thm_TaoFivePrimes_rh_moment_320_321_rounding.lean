-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_moment_320_321_rounding
-- name    : TaoFivePrimes.rh_moment_320_321_rounding
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:05:15.556157+00:00
-- url     : https://prove2.me/theorems/ba4b5cb4-64b5-4c37-8631-d03217cdd81b
-- title:
--   Rounded cached Mellin values for moments 320–321
-- statement:
--   For $j=320,321$, let $C_j$ be the stored integer and let $\widetilde Q_j=3\widetilde N_j/D_j$ be the cached rational Mellin quadrature rule. Then
--
--   $$
--   C_j\le10^{64}\widetilde Q_j<C_j+1.
--   $$
--
--   This exact rounding certificate concerns the rational rule; an enclosure of the true moment is separate.
-- source:
--   Derived from the proved all-index Mellin rule and cached integer identity. The theta-jet and Mellin framework is due to sometik179, https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; theta/Mellin foundations are due to Gabewhigham. The higher moment numerators are new.

import Definitions.Def_TaoFivePrimes_RHExtendedMomentData320to335
import Definitions.Def_TaoFivePrimes_RHExtendedMomentCachedNumerator

theorem TaoFivePrimes.rh_moment_320_321_rounding : ∀ n : Fin 2,
    let j := 320+0+n.val
    let c := TaoFivePrimes_RHExtendedMomentData320to335.getD (0+n.val) 0
    c*(RHNextMomentInteger.denominator j:ℤ) ≤ 3*(10^64:ℤ)*RHNextMomentCached.numerator j ∧
    3*(10^64:ℤ)*RHNextMomentCached.numerator j < (c+1)*(RHNextMomentInteger.denominator j:ℤ) := by sorry
