-- Prove2me | Theorems.Thm_SizeRamsey_tau4_iso
-- name    : SizeRamsey.tau4_iso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:19:12.220892+00:00
-- url     : https://prove2.me/theorems/d52fa903-c143-4c24-8506-885e1b5a1a03
-- title:
--   Size Ramsey: tau4 iso
-- statement:
--   The Size Ramsey construction uses the tau4 iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Basic.lean#L88-L93
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Basic.lean#L88-L93

module
public import Definitions.Def_SizeRamsey_Shared
public import Definitions.Def_SizeRamsey_Basic
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey

theorem SizeRamsey.tau4_iso
    {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) :
    tau4 G = tau4 H := by sorry
