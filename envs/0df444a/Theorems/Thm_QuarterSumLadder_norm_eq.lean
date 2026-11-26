-- Prove2me | Theorems.Thm_QuarterSumLadder_norm_eq
-- name    : QuarterSumLadder.norm_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:09:32.102287+00:00
-- url     : https://prove2.me/theorems/bd529977-42b3-5082-904c-80c9cd907422
-- title:
--   Quarter Sum Ladder: norm eq
-- statement:
--   The Quarter Sum Ladder construction uses the norm eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Ladder.lean#L27-L28
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Ladder.lean#L27-L28

module
public import Definitions.Def_QuarterSumLadder_WeightTwo
public import Definitions.Def_QuarterSumLadder_Arith
public import Definitions.Def_QuarterSumLadder_Ladder
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuarterSumLadder.norm_eq (z : GaussianInt) : z.norm = z.re ^ 2 + z.im ^ 2 := by sorry
