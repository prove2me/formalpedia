-- Prove2me | Theorems.Thm_Pr6453_native_helpers
-- name    : Pr6453.native_helpers
-- status  : Proved
-- author  : @gustasmickus
-- created : 2026-11-08T18:35:07.062709+00:00
-- url     : https://prove2.me/theorems/29fa3c3f-73e9-4e0f-8291-89c110807e3b
-- title:
--   PR #6453: the enumerated native helpers
-- statement:
--   The native helpers of PR #6453, enumerated by rank, and the distinct-map count.
--
--   The 562 helpers are enumerated explicitly — fourteen of rank 1, eight of rank 2, four of rank 3, one hundred and seven of rank 4, fifteen of rank 5, three of rank 6, nine of rank 7, thirty-nine of rank 8 and three hundred and sixty-three of rank 9 — and the statements check the total and each rank count against the certificate's histogram. The distinct-map count 2 941 is recorded separately because the maps themselves are not in the PR package: the receipt carries their number and the hash of the recipe payload that holds them.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4, RESULT.json (native.helpers, native.distinct_maps).

import Definitions.Def_Pr6453_Word
import Definitions.Def_Pr6453_WordNative

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Pr6453

theorem native_helpers :
    helperRanks.length = 562 ∧ rankCount 1 = 14 ∧ rankCount 2 = 8 ∧ rankCount 3 = 4 ∧
      rankCount 4 = 107 ∧ rankCount 5 = 15 ∧ rankCount 6 = 3 ∧ rankCount 7 = 9 ∧
      rankCount 8 = 39 ∧ rankCount 9 = 363 ∧ distinctMaps = 2941 := by
  sorry

end Pr6453
