-- Prove2me | Theorems.Thm_SizeRamsey_tau4_le_card
-- name    : SizeRamsey.tau4_le_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:18:01.580214+00:00
-- url     : https://prove2.me/theorems/ba2592a5-d46a-56c2-8821-e5f3b829f9c7
-- title:
--   Size Ramsey: tau4 le card
-- statement:
--   The Size Ramsey construction uses the tau4 le card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Basic.lean#L37-L42
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Basic.lean#L37-L42

module
public import Definitions.Def_SizeRamsey_Shared
public import Definitions.Def_SizeRamsey_Basic
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey

theorem SizeRamsey.tau4_le_card
    {V : Type*} [Fintype V]
    {G : SimpleGraph V} {S : Finset V}
    (hS : c4Transversal G S) :
    tau4 G ≤ S.card := by sorry
