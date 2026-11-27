-- Prove2me | Theorems.Thm_SizeRamsey_c4Transversal_map_iso
-- name    : SizeRamsey.c4Transversal_map_iso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:18:05.639967+00:00
-- url     : https://prove2.me/theorems/88ee482f-6cf3-47ab-b60b-c3f35684c37b
-- title:
--   Size Ramsey: c4 Transversal map iso
-- statement:
--   The Size Ramsey construction uses the c4 Transversal map iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Basic.lean#L70-L77
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Basic.lean#L70-L77

module
public import Definitions.Def_SizeRamsey_Shared
public import Definitions.Def_SizeRamsey_Basic
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey

theorem SizeRamsey.c4Transversal_map_iso
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) {T : Finset W} (hT : c4Transversal H T) :
    c4Transversal G (T.map e.symm.toEquiv.toEmbedding) := by sorry
