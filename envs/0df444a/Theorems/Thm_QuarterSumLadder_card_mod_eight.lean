-- Prove2me | Theorems.Thm_QuarterSumLadder_card_mod_eight
-- name    : QuarterSumLadder.card_mod_eight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:12:21.988065+00:00
-- url     : https://prove2.me/theorems/a1cb2173-8d67-5e6f-b6fa-6dfcf1e9528a
-- title:
--   Quarter Sum Ladder: card mod eight
-- statement:
--   `#{0 < m < p : m ≡ r (mod 8)} = (p - 1)/8` for `1 ≤ r ≤ 7`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Boundary.lean#L35-L53
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Boundary.lean#L35-L53

module
public import Definitions.Def_QuarterSumLadder_Ladder
public import Definitions.Def_QuarterSumLadder_Boundary
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuarterSumLadder.card_mod_eight (hp8 : p % 8 = 1) {r : ℕ} (hr1 : 1 ≤ r) (hr7 : r ≤ 7) :
    (univ.filter fun x : ZMod p => x.val % 8 = r).card = (p - 1) / 8 := by sorry
