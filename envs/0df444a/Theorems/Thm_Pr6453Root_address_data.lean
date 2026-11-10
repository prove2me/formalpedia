-- Prove2me | Theorems.Thm_Pr6453Root_address_data
-- name    : Pr6453Root.address_data
-- status  : Proved
-- author  : @gustasmickus
-- created : 2026-11-09T09:01:55.196195+00:00
-- url     : https://prove2.me/theorems/d4a4a5ac-bf77-4d90-a641-61c1409c92a4
-- title:
--   PR #6453: the root's address data
-- statement:
--   The root's address structure: the coefficient address is (sign, mask, field) with two signs, sixteen masks over four full stages and six fields; the masks are read from the mask table; two signs times sixteen masks times thirty-six field entries is the certificate's 1152.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4, ROOT.json.

import Definitions.Def_Pr6453RootAddress

set_option autoImplicit false

namespace Pr6453Root

theorem address_data :
    Fintype.card Mask = 16 ∧ Fintype.card Address = 192 ∧ 2 * Fintype.card Mask * 36 = 1152 := by
  sorry

end Pr6453Root
