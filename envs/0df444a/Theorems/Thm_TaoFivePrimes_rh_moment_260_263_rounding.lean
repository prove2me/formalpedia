-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_moment_260_263_rounding
-- name    : TaoFivePrimes.rh_moment_260_263_rounding
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:13:23.449794+00:00
-- url     : https://prove2.me/theorems/bd9d1a86-e06d-40d9-ab08-ade5b004605a
-- title:
--   Exact rounded cached Mellin values for moments 260–263
-- statement:
--   For each moment index $260\le j\le263$, let $C_j$ be the stored integer and let $\widetilde Q_j=3\widetilde N_j/D_j$ be the cached rational Mellin rule. Then
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

theorem TaoFivePrimes.rh_moment_260_263_rounding : ∀ n : Fin 4,
    let j := 256+4+n.val
    let c := TaoFivePrimes_RHExtendedMomentData256to271.getD (4+n.val) 0
    c*(RHNextMomentInteger.denominator j:ℤ) ≤ 3*(10^64:ℤ)*RHNextMomentCached.numerator j ∧
    3*(10^64:ℤ)*RHNextMomentCached.numerator j < (c+1)*(RHNextMomentInteger.denominator j:ℤ) := by sorry
