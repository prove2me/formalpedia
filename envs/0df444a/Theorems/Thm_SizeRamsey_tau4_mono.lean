-- Prove2me | Theorems.Thm_SizeRamsey_tau4_mono
-- name    : SizeRamsey.tau4_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:18:09.664972+00:00
-- url     : https://prove2.me/theorems/7b7fbda6-3ea9-4619-b605-ad8901064f93
-- title:
--   Size Ramsey: tau4 mono
-- statement:
--   The Size Ramsey construction uses the tau4 mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Basic.lean#L53-L60
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Basic.lean#L53-L60

module
public import Definitions.Def_SizeRamsey_Shared
public import Definitions.Def_SizeRamsey_Basic
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey

theorem SizeRamsey.tau4_mono
    {V : Type*} [Fintype V]
    {G H : SimpleGraph V} (h : G ≤ H) :
    tau4 G ≤ tau4 H := by sorry
