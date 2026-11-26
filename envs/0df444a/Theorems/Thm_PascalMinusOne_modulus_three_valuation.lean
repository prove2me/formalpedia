-- Prove2me | Theorems.Thm_PascalMinusOne_modulus_three_valuation
-- name    : PascalMinusOne.modulus_three_valuation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:21:48.899996+00:00
-- url     : https://prove2.me/theorems/bcb0f1ee-d8bd-505f-bf7c-a1e9dbea5e09
-- title:
--   Pascal Minus One: modulus three valuation
-- statement:
--   Complete prime-by-prime valuation formula for `G(N;3)`.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/SmallModuli.lean#L123-L153
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/SmallModuli.lean#L123-L153

import Definitions.Def_PascalMinusOne_PlusOne
import Definitions.Def_PascalMinusOne_Scaling
import Definitions.Def_PascalMinusOne_SmallModuli
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.modulus_three_valuation
    {p N : ℕ} (hp : p.Prime) (h3N : 3 ∣ N) (hN : 3 < N) :
    padicValNat p (G N 3) = modulusThreeExpectedValuation p N := by sorry
