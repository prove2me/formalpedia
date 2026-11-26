-- Prove2me | Theorems.Thm_PascalMinusOne_modulus_four_valuation
-- name    : PascalMinusOne.modulus_four_valuation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:22:06.59943+00:00
-- url     : https://prove2.me/theorems/3a4caa5d-fad4-53f6-9969-b6f84ae14861
-- title:
--   Pascal Minus One: modulus four valuation
-- statement:
--   Complete prime-by-prime valuation formula for `G(N;4)`.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/SmallModuli.lean#L156-L186
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/SmallModuli.lean#L156-L186

import Definitions.Def_PascalMinusOne_PlusOne
import Definitions.Def_PascalMinusOne_Scaling
import Definitions.Def_PascalMinusOne_SmallModuli
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.modulus_four_valuation
    {p N : ℕ} (hp : p.Prime) (h4N : 4 ∣ N) (hN : 4 < N) :
    padicValNat p (G N 4) = modulusFourExpectedValuation p N := by sorry
