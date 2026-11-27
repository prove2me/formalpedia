-- Prove2me | Theorems.Thm_SizeRamsey_F17_connected
-- name    : SizeRamsey.F17_connected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:25:15.234097+00:00
-- url     : https://prove2.me/theorems/f24028f6-6562-5bef-8282-f71e3725b75d
-- title:
--   Size Ramsey: F17 connected
-- statement:
--   The Size Ramsey construction uses the F17 connected property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Upper.lean#L147-L165
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Upper.lean#L147-L165

module
public import Definitions.Def_SizeRamsey_AInterface
public import Definitions.Def_SizeRamsey_Upper
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey

theorem SizeRamsey.F17_connected :
    F17.Connected := by sorry
