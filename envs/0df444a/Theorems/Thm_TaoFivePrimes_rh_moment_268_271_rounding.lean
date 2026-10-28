-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_moment_268_271_rounding
-- name    : TaoFivePrimes.rh_moment_268_271_rounding
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:14:05.618547+00:00
-- url     : https://prove2.me/theorems/51a66bd9-e660-445d-9a84-ae9e2c51590e
-- title:
--   Exact rounded cached Mellin values for moments 268–271
-- statement:
--   For each moment index $268\le j\le271$, let $C_j$ be the stored integer and let $\widetilde Q_j=3\widetilde N_j/D_j$ be the cached rational Mellin rule. Then
--
--   $$
--   C_j\le10^{64}\widetilde Q_j<C_j+1.
--   $$
--
--   This exact integer rounding certificate is a numerical input to a moment enclosure. It does not alone assert an error bound for the true Mellin moment.
-- source:
--   Exact integer computation from the rational Mellin and theta-jet framework of sometik179, Prove2Me c9908072-d99a-4431-aad8-a72c6352619a, https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; theta/Mellin foundations by Gabewhigham. The listed rounded indices are new.

import Definitions.Def_TaoFivePrimes_RHExtendedMomentData256to271
import Definitions.Def_TaoFivePrimes_RHExtendedMomentCachedNumerator

theorem TaoFivePrimes.rh_moment_268_271_rounding : ∀ n : Fin 4,
    let j := 256+12+n.val
    let c := TaoFivePrimes_RHExtendedMomentData256to271.getD (12+n.val) 0
    c*(RHNextMomentInteger.denominator j:ℤ) ≤ 3*(10^64:ℤ)*RHNextMomentCached.numerator j ∧
    3*(10^64:ℤ)*RHNextMomentCached.numerator j < (c+1)*(RHNextMomentInteger.denominator j:ℤ) := by sorry
