-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_extended_moment_correlations_1
-- name    : TaoFivePrimes.rh_extended_moment_correlations_1
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:09:00.589343+00:00
-- url     : https://prove2.me/theorems/4955ebeb-e153-4db1-9bf9-5fef15f4ac53
-- title:
--   Exact Mellin jet correlations for panels 4–7
-- statement:
--   For every panel index $4\le i\le7$ and every $0\le m<184$, the stored integer $B_{i,m}$ equals the finite correlation of the published theta-jet coefficients with the common-denominator integration weights:
--
--   $$
--   B_{i,m}=\sum_{\ell=0}^{183-m} H_{i,\ell}W_{m+\ell}.
--   $$
--
--   Here $H_{i,\ell}$ is the integer theta-jet sum and $W_r$ is the integer integration weight. The verified table is reusable at every moment order.
-- source:
--   Exact finite arithmetic computed from the published theta-jet certificate of sometik179, Prove2Me c9908072-d99a-4431-aad8-a72c6352619a, https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; theta/Mellin foundations by Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHExtendedMomentIntegerRule
import Definitions.Def_TaoFivePrimes_RHExtendedMomentCorrelations1

theorem TaoFivePrimes.rh_extended_moment_correlations_1 : ∀ i : Fin 4, ∀ m : Fin 184,
    RHNextMomentInteger.correlation (4+i.val) m.val =
      ((TaoFivePrimes_RHExtendedMomentCorrelations1.getD i.val []).getD m.val 0) := by sorry
