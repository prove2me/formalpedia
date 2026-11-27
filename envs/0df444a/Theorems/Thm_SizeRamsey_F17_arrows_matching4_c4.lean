-- Prove2me | Theorems.Thm_SizeRamsey_F17_arrows_matching4_c4
-- name    : SizeRamsey.F17_arrows_matching4_c4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:25:20.638842+00:00
-- url     : https://prove2.me/theorems/167580b4-3668-5200-a6fd-1320994b2ded
-- title:
--   Size Ramsey: F17 arrows matching4 c4
-- statement:
--   The Size Ramsey construction uses the F17 arrows matching4 c4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Upper.lean#L187-L207
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Upper.lean#L187-L207

module
public import Definitions.Def_SizeRamsey_AInterface
public import Definitions.Def_SizeRamsey_Upper
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey

theorem SizeRamsey.F17_arrows_matching4_c4 :
    ArrowsMatching4C4 F17 := by sorry
