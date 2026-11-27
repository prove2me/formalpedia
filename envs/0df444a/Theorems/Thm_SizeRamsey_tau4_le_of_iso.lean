-- Prove2me | Theorems.Thm_SizeRamsey_tau4_le_of_iso
-- name    : SizeRamsey.tau4_le_of_iso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:18:02.946969+00:00
-- url     : https://prove2.me/theorems/1b069797-b3f0-564d-8e17-f26527b69b94
-- title:
--   Size Ramsey: tau4 le of iso
-- statement:
--   The Size Ramsey construction uses the tau4 le of iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Basic.lean#L79-L86
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Basic.lean#L79-L86

module
public import Definitions.Def_SizeRamsey_Shared
public import Definitions.Def_SizeRamsey_Basic
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey

theorem SizeRamsey.tau4_le_of_iso
    {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) :
    tau4 G ≤ tau4 H := by sorry
