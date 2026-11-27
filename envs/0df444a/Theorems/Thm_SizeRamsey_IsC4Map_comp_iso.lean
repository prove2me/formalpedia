-- Prove2me | Theorems.Thm_SizeRamsey_IsC4Map_comp_iso
-- name    : SizeRamsey.IsC4Map.comp_iso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:18:00.559077+00:00
-- url     : https://prove2.me/theorems/2c80b5a7-4eae-4b58-a645-1cc31e985acd
-- title:
--   Is C4 Map: comp iso
-- statement:
--   The Is C4 Map construction uses the comp iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Basic.lean#L62-L68
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Basic.lean#L62-L68

module
public import Definitions.Def_SizeRamsey_Shared
public import Definitions.Def_SizeRamsey_Basic
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey

theorem SizeRamsey.IsC4Map.comp_iso
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) {f : Fin 4 → V} (hf : IsC4Map G f) :
    IsC4Map H (e ∘ f) := by sorry
