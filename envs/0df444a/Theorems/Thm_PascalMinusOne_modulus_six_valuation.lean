-- Prove2me | Theorems.Thm_PascalMinusOne_modulus_six_valuation
-- name    : PascalMinusOne.modulus_six_valuation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:22:13.267232+00:00
-- url     : https://prove2.me/theorems/13162c0a-6813-5f2a-906a-33b3817b3a10
-- title:
--   Pascal Minus One: modulus six valuation
-- statement:
--   Complete prime-by-prime valuation formula for `G(N;6)`.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/SmallModuli.lean#L189-L245
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/SmallModuli.lean#L189-L245

import Definitions.Def_PascalMinusOne_PlusOne
import Definitions.Def_PascalMinusOne_Scaling
import Definitions.Def_PascalMinusOne_SmallModuli
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.modulus_six_valuation
    {p N : ℕ} (hp : p.Prime) (h6N : 6 ∣ N) (hN : 6 < N) :
    padicValNat p (G N 6) = modulusSixExpectedValuation p N := by sorry
