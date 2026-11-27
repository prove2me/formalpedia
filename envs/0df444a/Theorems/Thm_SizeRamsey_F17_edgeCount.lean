-- Prove2me | Theorems.Thm_SizeRamsey_F17_edgeCount
-- name    : SizeRamsey.F17_edgeCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:18:02.826389+00:00
-- url     : https://prove2.me/theorems/510cdd14-d07f-5ea8-8947-9f9ae938a9f5
-- title:
--   Size Ramsey: F17 edge Count
-- statement:
--   The Size Ramsey construction uses the F17 edge Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Basic.lean#L33-L35
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Basic.lean#L33-L35

module
public import Definitions.Def_SizeRamsey_Shared
public import Definitions.Def_SizeRamsey_Basic
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey

theorem SizeRamsey.F17_edgeCount : edgeCount F17 = 17 := by sorry
